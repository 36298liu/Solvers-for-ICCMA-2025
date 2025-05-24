/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>
#include <zlib.h>
#include <vector>
#include <sstream>

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/core/Solver.h"

#include "argsemsat.h"

using namespace Minisat;

//=================================================================================================


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        solver->printStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:


int minisatlib(char *in, std::vector<int> *sol)
{
    try {
        //setX86FPUPrecision();

        //
        // Extra options:
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);
        
        Solver S;

        if (debug)
        {
        	cerr << "opt_var_decay " << S.var_decay << endl;
        	cerr << "opt_clause_decay " << S.clause_decay << endl;
        	cerr << "opt_random_var_freq " << S.random_var_freq << endl;
        	cerr << "opt_random_seed " << S.random_seed << endl;
        	cerr << "opt_ccmin_mode " << S.ccmin_mode << endl;
        	cerr << "opt_phase_saving " << S.phase_saving << endl;
        	cerr << "opt_rnd_init_act " << S.rnd_init_act << endl;
        	cerr << "opt_luby_restart " << S.luby_restart << endl;
        	cerr << "opt_restart_first " << S.restart_first << endl;
        	cerr << "opt_restart_inc " << S.restart_inc << endl;
        	cerr << "opt_garbage_frac " << S.garbage_frac << endl;
        	cerr << "opt_min_leartns_lim " << S.min_learnts_lim << endl;
        	cerr << "opt_rnd_pol " << S.rnd_pol << endl;
        	cerr << "opt_default_upol " << opt_default_upol << endl;
        }

        double initial_time = cpuTime();

        S.verbosity = verb;
        
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        //sigTerm(SIGINT_exit);

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);
        
        
        parse_DIMACS_main(in, S, strictp);


        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
            printf("|                                                                             |\n"); }
 
        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        //sigTerm(SIGINT_interrupt);
       
        if (!S.simplify()){
/*            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by unit propagation\n");
                S.printStats();
                printf("\n"); }*/
            return(20);
        }
        
        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
        if (S.verbosity > 0){
            S.printStats();
            printf("\n"); }
        if (true){
            if (ret == l_True){
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                    {
                    	if (S.model[i] == l_True)
                    		sol->push_back(i+1);
                    	else
                    		sol->push_back(-1*(i+1));
                    }
            }
        }

        if (ret == l_True)
        	return 10;
        else if (ret == l_False)
        	return 20;
        else
        	return 0;

    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
