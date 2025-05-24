/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
 
Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Maple_LCM, Based on MapleCOMSPS_DRUP -- Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , "An effective learnt clause minimization approach for cdcl sat solvers," in IJCAI-2017, 2017, pp. to–appear.
 
Maple_LCM_Dist, Based on Maple_LCM -- Copyright (c) 2017, Fan Xiao, Chu-Min LI, Mao Luo: using a new branching heuristic called Distance at the beginning of search
 
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
#include <vector>
#include <sstream>
#include <signal.h>
#include <zlib.h>

#include "amsat/utils/System.h"
#include "amsat/utils/ParseUtils.h"
#include "amsat/utils/Options.h"
#include "amsat/core/Dimacs.h"
#include "amsat/core/Solver.h"
#include "argsemsat.h"

using namespace Minisat;

//=================================================================================================

 

static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("c *** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        solver->printStats();
        printf("\n"); printf("c *** INTERRUPTED ***\n"); }
    _exit(1); }

// 主函数：将原来的主函数重构为库函数
int minisatlib(char *inFile, std::vector<int> *sol)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        //printf("c This is COMiniSatPS.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        //printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        
        Solver S;
        double initial_time = cpuTime();
        S.verbosity = 0;
        solver = &S;

        // Use signal handlers that forcibly quit until the solver will be able to respond to
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            }
        }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            }
        }
        
        if (S.verbosity > 0){
            printf("c ============================[ Problem Statistics ]=============================\n");
            printf("c |                                                                             |\n");
        }

        // Open the input file using gzopen
        // gzFile in = gzopen(inFile, "rb");
        // if (in == NULL) {
        //     printf("c ERROR! Could not open file: %s\n", inFile);
        //     exit(1);
        // }
        
        // Pass the gzFile to parse_DIMACS
        parse_DIMACS_main(inFile,S);
        
        // // Close the gzFile
        // gzclose(in);

        // Initialize res to nullptr
        // FILE* res = nullptr;
        // if (sol != nullptr) {
        //     res = fopen("output.txt", "wb");
        // }
        
        if (S.verbosity > 0){
            printf("c |  Number of variables:  %12d                                         |\n", S.nVars());
            printf("c |  Number of clauses:    %12d                                         |\n", S.nClauses());
        }

        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("c |  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
            printf("c |                                                                             |\n");
        }

        // signal(SIGINT, SIGINT_interrupt);
        // signal(SIGXCPU,SIGINT_interrupt);

        if (!S.simplify()){
            // if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            // if (S.verbosity > 0){
            //     printf("c ===============================================================================\n");
            //     printf("c Solved by unit propagation\n");
            //     // printStats(S); // Remove or implement this function
            //     printf("\n");
            // }
            // printf("s UNSATISFIABLE\n");
            exit(20);
        }
        
        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
        if (S.verbosity > 0){
            S.printStats(); // Uncomment if printStats is available
            printf("\n");
        }
        // printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s UNKNOWN\n");

        if (true){
            if (ret == l_True){
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                    {
                        if (S.model[i] == l_True) {
                            sol->push_back(i + 1);
                        } else {
                            sol->push_back(-1 * (i + 1));
                        }
                    }
                    //printf("求解完成");
            }
        }

        if (ret == l_True)
        	return 10;
        else if (ret == l_False)
        	return 20;
        else
        	return 0; 
    } catch (OutOfMemoryException&){
        printf("c ===============================================================================\n");
        printf("s UNKNOWN\n");
        exit(0);
    }
}
