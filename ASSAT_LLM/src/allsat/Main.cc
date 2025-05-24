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

#include <signal.h>
#include <zlib.h>
#include <cinttypes>
#include <fstream>
#include <iostream>
#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "AllClauseAllSATSolver.h"
#include "NaiveAllSATSolver.h"
#include "SmartBlockingAllSATSolver.h"
#include "AccessSolver.h"

std::vector<std::vector <int> *> *models;
std::vector<std::vector <int> *> *blocking;

using namespace Minisat;
static std::string _inputFile;
static double initial_time = 0.0;




//=================================================================================================

void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %" PRIu64"\n", solver.starts);
    printf("conflicts             : %-12" PRIu64"   (%.0f /sec)\n", solver.conflicts , solver.conflicts /cpu_time);
    printf("decisions             : %-12" PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions /cpu_time);
    printf("propagations          : %-12" PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("conflict literals     : %-12" PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0)
	printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}

static Allsat::AccessSolver* solver;
static Allsat::AllSATSolver* _allSATSolver;
static Allsat::AllSATSolver* _toCNFSolver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum)
{
    solver->interrupt();
}

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum)
{
    printf("\n");
    printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0) {
	printStats(*solver);
	printf("\n");
	printf("*** INTERRUPTED ***\n");
    }
    printf("RESULT: %s INTERRUPTED\n", _inputFile.c_str());
    _exit(1);
}
static void SIGCPULIMIT_exit(int signum)
{
    printf("\n");
    if (solver->verbosity > 0) {
	printStats(*solver);
	printf("\n\n");
    }
    std::cout<<"RESULT: " << _inputFile <<" TIMEOUT"
	    << " " << _allSATSolver->_stats.numVariables
	    << " " << _allSATSolver -> _stats.numClauses
	    << " " << _allSATSolver->_stats.numBlockingClauses 
	    << " " << _allSATSolver->_stats.numBlockingLits
	    << " "<< (cpuTime() - initial_time)
	    << std::endl;
    _exit(1);
}

static void signalKilled(int signum)
{
    if (solver->verbosity > 0) {
    printf("\n");
	printStats(*solver);
	printf("\n\n");
    }
    std::cout << "INDETERMINATE" << std::endl;
    _exit(1);
}


//=================================================================================================
// Main:

int allsatlib(char *in, std::vector<std::vector <int> *> *sol, std::vector<std::vector <int> *> *block)
{
	models = new std::vector<std::vector <int> *>();
	blocking = new std::vector<std::vector <int> *>();

    try {
	setUsageHelp(
	        "USAGE: %s [options] <input-file> <blocking-clause-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
	// printf("This is MiniSat 2.0 beta\n");

#if defined(__linux__)
	fpu_control_t oldcw, newcw;
	_FPU_GETCW(oldcw);
	newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
	_FPU_SETCW(newcw);
	//fprintf(stderr, "WARNING: for repeatability, setting FPU to use double precision\n");
#endif
	// Extra options:
	//
	IntOption verb("MAIN", "verb",
	        "Verbosity level (0=silent, 1=some, 2=more, 3=even more).", 0,
	        IntRange(0, 3));
	IntOption cpu_lim("MAIN", "cpu-lim",
	        "Limit on CPU time allowed in seconds.\n", INT32_MAX,
	        IntRange(0, INT32_MAX));
	IntOption mem_lim("MAIN", "mem-lim",
	        "Limit on memory usage in megabytes.\n", INT32_MAX,
	        IntRange(0, INT32_MAX));
	StringOption allsat_type("MAIN", "allsat-type",
	        "The types of AllSAT to run, can be Naive, AllClause and Smart",
	        "Smart");
	IntOption bc_lim("MAIN", "bc-lim","Limit on number of blocking clauses,\n", INT32_MAX, IntRange(0, INT32_MAX));
	BoolOption dec_only("MAIN", "dec-only", "generate decision only blocking clauses\n", false);
    BoolOption reachability("MAIN", "-reachability", "compute 1-step reachability.", false);

	//parseOptions(argc, argv, true);

	Allsat::AccessSolver S;
    Allsat::AccessSolver S2;
	initial_time = cpuTime();

	S2.verbosity = S.verbosity = verb;

	solver = &S;
	// Use signal handlers that forcibly quit until the solver will be able to respond to
	// interrupts:
    if(!reachability) {
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU, SIGCPULIMIT_exit);
    } else {
        signal(SIGINT, signalKilled);
        signal(SIGXCPU, signalKilled);
    }

	// Set limit on CPU-time:
	if (cpu_lim != INT32_MAX) {
	    rlimit rl;
	    getrlimit(RLIMIT_CPU, &rl);
	    if (rl.rlim_max == RLIM_INFINITY
		    || (rlim_t) cpu_lim < rl.rlim_max) {
		rl.rlim_cur = cpu_lim;
		if (setrlimit(RLIMIT_CPU, &rl) == -1)
		    printf("WARNING! Could not set resource limit: CPU-time.\n");
	    }
	}

	// Set limit on virtual memory:
	if (mem_lim != INT32_MAX) {
	    rlim_t new_mem_lim = (rlim_t) mem_lim * 1024 * 1024;
	    rlimit rl;
	    getrlimit(RLIMIT_AS, &rl);
	    if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max) {
		rl.rlim_cur = new_mem_lim;
		if (setrlimit(RLIMIT_AS, &rl) == -1)
		    fprintf(stderr, "WARNING! Could not set resource limit: Virtual memory.\n");
	    }
	}

	/*if (argc == 1) {
	    fprintf(stderr, "Reading from standard input... Use '--help' for help.\n");
	    _inputFile = "-";
	} else {
	    _inputFile = argv[1];
	}*/

	/*gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
	if (in == NULL)
	    fprintf(stderr, "ERROR! Could not open file: %s\n",
		    argc == 1 ? "<stdin>" : argv[1]), exit(1);

	if (S.verbosity > 0) {
	    printf("============================[ Problem Statistics ]=============================\n");
	    printf("|                                                                             |\n");
	}*/

    parse_DIMACS_main(in, S, false);

//	gzclose(in);
//	FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
/*	std::ofstream *pof = (argc >= 3) ? new std::ofstream(argv[2]) : NULL;
	if (S.verbosity > 0) {
	    printf("|  Number of variables:  %12d                                         |\n", S.nVars());
	    printf("|  Number of clauses:    %12d                                         |\n", S.nClauses());
	}

	double parsed_time = cpuTime();
	if (S.verbosity > 0) {
	    printf("|  Parse time:           %12.2f s                                       |\n",
		    parsed_time - initial_time);
	    printf("|                                                                             |\n");
	}*/
	Allsat::AllSATSolver * allSATSolver;
    Allsat::AllSATSolver * toCNFSolver;
	std::string allsat_type_str(allsat_type);
	if (strncmp(allsat_type, "Naive",5) == 0) {
	    allSATSolver = new Allsat::NaiveAllSATSolver(&S);
        if(reachability) {
            toCNFSolver = new Allsat::NaiveAllSATSolver(&S2);
        }
	} else if (strncmp(allsat_type, "Smart", 5) == 0) {
	    allSATSolver = new Allsat::SmartBlockingAllSATSolver(&S,Allsat::GREEDYSLOW);
        if(reachability) {
            toCNFSolver = new Allsat::SmartBlockingAllSATSolver(&S2, Allsat::GREEDYSLOW);
        }
	} else if (strncmp(allsat_type, "AllClause", 9) == 0) {
	    allSATSolver = new Allsat::AllClauseAllSATSolver(&S, Allsat::GREEDYSLOW);
        if(reachability) {
            toCNFSolver = new Allsat::AllClauseAllSATSolver(&S2, Allsat::GREEDYSLOW);
        }
	} else {
	    fprintf(stderr, "Invalid option for allsat_type: %s", allsat_type.operator const char*());
	    exit (-1);
	}
	allSATSolver-> setMaxBlockingClause(bc_lim);
	_allSATSolver = allSATSolver;

    if(reachability) {
        toCNFSolver-> setMaxBlockingClause(bc_lim);
        toCNFSolver->addVars(&S);
        _toCNFSolver = toCNFSolver;
    }

	// Change to signal-handlers that will only notify the solver and allow it to terminate
	// voluntarily:
	signal(SIGINT, SIGINT_interrupt);
	signal(SIGXCPU, SIGINT_interrupt);

	if (!S.simplify()) {
/*	    if (S.verbosity > 0) {
		printf("===============================================================================\n");
		printf("Solved by unit propagation\n");
		printStats(S);
		printf("\n");
	    }
	    printf("UNSATISFIABLE\n");*/
	    return 20;
	}

    bool finished = false;
    if(reachability) {
        finished = allSATSolver->solveReachability(toCNFSolver);
    } else {
	    finished = allSATSolver->solve();
    }

    /*
	std::cout<<"RESULT: " << argv[1] 
	    <<" " << (finished? "SUCCESS" : "FAIL") 
	    <<" " << allsat_type_str
	    <<" " << (allSATSolver->_stats.firstSATCPUTime > 0 ? "SAT_BUT_INCOMPLETE_ALLSAT" : "SAT_UNKNOWN")
	    << " " << allSATSolver->_stats.numVariables
	    << " " << allSATSolver -> _stats.numClauses
	    << " " << (allSATSolver -> _stats.numSATs > 0? (allSATSolver -> _stats.numTotalDecisions *1.0 / allSATSolver -> _stats.numSATs) : 0.0)
	    << " " << (allSATSolver -> _stats.numSATs > 0 ? (allSATSolver-> _stats.numTotalUndecidedVariables *1.0 / allSATSolver -> _stats.numSATs) : 0.0)
	    << " " << allSATSolver->_stats.numBlockingClauses 
	    << " " << allSATSolver->_stats.numBlockingLits
	    << " " << allSATSolver -> _stats.numSolutionLits
	    << " " << allSATSolver -> _stats.firstSATCPUTime
	    << " " << allSATSolver -> _stats.numSATs
	    << " "<< (cpuTime() - initial_time)
	    << std::endl;
    */
    if(!finished) {
    	return 0;
        //std::cout << "INDETERMINATE" << std::endl;
    } else {
        //std::cout << "COMPLETE" << std::endl;
        //std::cout << allSATSolver->_stats.numBlockingClauses << " " << allSATSolver->_stats.numBlockingLits << std::endl;
        //std::cout << toCNFSolver->_stats.numBlockingClauses << " " << toCNFSolver->_stats.numBlockingLits << std::endl;
        //std::cout << cpuTime() - initial_time << std::endl;

    	//std::cout << models->size() << std::endl;

		for (std::vector<std::vector <int > *>::iterator m = models->begin(); m != models->end(); m++)
		{
			sol->push_back((*m));
		}

		if (block != NULL){
			for (std::vector<std::vector <int> *>::iterator b = blocking->begin(); b != blocking->end(); b++)
			{
				block->push_back((*b));
			}
		}

    	return 10;
    }
    /*if(pof != NULL) {
        if(reachability) {
            toCNFSolver -> dumpAllSATBlockingClauses(*pof);
        } else {
            allSATSolver -> dumpAllSATBlockingClauses(*pof);
        }
    }*/
/*
#ifdef NDEBUG
//	exit(ret == l_True ? 10 : ret == l_False ? 20 : 0); // (faster than "return", which will invoke the destructor for 'Solver')
	exit (0);
#else
	return ( 0);
#endif*/
    } catch (OutOfMemoryException&) {
	//printf("===============================================================================\n");
	//printf("INDETERMINATE\n");
	return(0);
    }
}
