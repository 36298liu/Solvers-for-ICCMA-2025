/**
 * @file 		argsemsat.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef _ArgSemSAT_H
#define	_ArgSemSAT_H

#include <cmath>
#include <cstdio>
#include <fstream>
#include <cstdlib>
#include <stdlib.h>
#include <vector>
#include <array>
#include <time.h>

#include <algorithm>
#include <iostream>
#include <sstream>
#include <cstring>
#include <string>
#include <cassert>
#include <set>

#define DIMBUFFER 100000

using namespace std;


#define HG(a) static const char *hgrev = a;

#define PUBLIC_RELEASE "1.0.5"
#ifndef PUBLIC_RELEASE
#include "hgversion.h"
#else
#define HG(a) static const char *hgrev = a;
HG("Version: " PUBLIC_RELEASE);
#endif



#include "AF.h"
#include "OrClause.h"
#include "SATFormulae.h"
#include "SetArguments.h"
#include "Labelling.h"
#include "Semantics.h"
#include "CompleteSemantics.h"
#include "PreferredSemantics.h"
#include "GroundedSemantics.h"
#include "StableSemantics.h"
#include "SemistableSemantics.h"
#include "Encoding.h"
#include "ConfigurationPreferred.h"
#include "ConfigurationStable.h"
#include "ConfigurationSemiStable.h"
#include "ConfigurationComplete.h"
#include "amsat/utils/Options.h"


extern bool debug;
extern bool externalsat;
extern string satsolver;
extern string inputfile;
extern string semantics;
extern string problem;
extern Encoding global_enc;
extern ConfigurationPreferred confPreferred;
extern ConfigurationStable confStable;
extern ConfigurationSemiStable confSemiStable;
extern ConfigurationComplete confComplete;
extern string defaultsolver;
extern string path;
extern string argumentDecision;

extern Minisat::DoubleOption 	opt_var_decay;
extern Minisat::DoubleOption 	opt_clause_decay;
extern Minisat::DoubleOption 	opt_random_var_freq;
extern Minisat::DoubleOption 	opt_random_seed;
extern Minisat::IntOption 		opt_ccmin_mode;
extern Minisat::IntOption 		opt_phase_saving;
extern Minisat::BoolOption 		opt_rnd_init_act;
extern Minisat::BoolOption 		opt_luby_restart;
extern Minisat::IntOption 		opt_restart_first;
extern Minisat::DoubleOption 	opt_restart_inc;
extern Minisat::DoubleOption 	opt_garbage_frac;
extern Minisat::IntOption		opt_min_learnts_lim;

//extern Minisat::BoolOption 		opt_rnd_pol;
//extern Minisat::BoolOption 	opt_default_upol;

//extern static Minisat::DoubleOption  opt_clause_decay;
//extern static Minisat::DoubleOption  opt_random_var_freq;

//const string precosat = "PRECOSAT";
//const string glucose = "GLUCOSE";

const string complete_string_const = "CO";
const string preferred_string_const = "PR";
//const string preferred_df_string_const = "preferred-df";
const string grounded_string_const = "GR";
//const string grounded_poly_string_const = "grounded-poly";
const string stable_string_const = "ST";
const string semistable_string_const = "SST";


const string credulous = "DC";
const string skeptical = "DS";
const string enumerateall = "EE";
const string enumeratesome = "SE";

const string acceptedformats [] = {"apx"};
#define NUM_FORMATS 1
const string acceptedproblems [] = {"DC-CO",
									"DC-GR",
									"DC-PR",
									"DC-ST",
									"DC-SST", // semi-stable added
									"DS-CO",
									"DS-GR",
									"DS-PR",
									"DS-ST",
									"DS-SST", // semi-stable added
									"EE-CO",
									"EE-GR",
									"EE-PR",
									"EE-ST",
									"EE-SST", // semi-stable added
									"SE-CO",
									"SE-GR",
									"SE-PR",
									"SE-ST",
									"SE-SST"
									};
#define NUM_PROBLEMS 20

#define PARSE_CONTINUE 0
#define PARSE_EXIT 10
#define PARSE_ERROR -10
#define PARSE_UNABLE -20

//extern int (*SatSolver)(stringstream *, int, int, vector<int> *);

extern bool manualopt;
extern time_t start;

bool parse_solution_aspartix(set<set<string> > *, const char *);

int
parseParams(int argc, char *argv[]);

void showHelp(const char *);
void authorInfo(const char *);
void printArray(const string [], int dim);
bool isInArray(string, const string[], int);

#endif	/* _ArgSemSAT_H */

int precosat_lib(stringstream *the_cnf, int num_var, int num_cl, vector<int> *result);

int glucose_lib(stringstream *the_cnf, int num_var, int num_cl, vector<int> *result);
