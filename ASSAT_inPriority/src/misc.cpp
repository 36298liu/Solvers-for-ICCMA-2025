/**
 * @file 		misc.cpp
 * @brief 		Miscellanea functions
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "argsemsat.h"
#include <sys/stat.h>

/**
 * @brief 				Function checking the existence of a file
 * @param[in] filename	Pointer to a `const char` containing the name of the file
 * @retval bool
 */
bool fexists(const char *filename)
{
	struct stat buffer;
	return (stat(filename, &buffer) == 0);
}

void printArray(const string arr[], int dim)
{
	int i = 0;
	cout << "[";
	for (i = 0; i < dim; i++)
	{
		cout << arr[i];
		if (i != dim - 1)
			cout << ",";
	}
	cout << "]" << endl;
}

bool isInArray(string el, const string arr[], int dim)
{
	int i = 0;
	for (i = 0; i < dim; i++)
	{
		if (arr[i].compare(el) == 0)
			return true;
	}
	return false;
}

/**
 * @brief				Function for parsing the parameters
 * @details				This function does not return any value. It fills global variables according to
 * 						the received parameters.
 * @param[in] argc		`int` containing the numbers of parameters
 * @param[in] argv		List of parameters
 * @retval int			  0: everything is fine
 * 						 10: exit the program
 * 						-10: error
 * 						-20: unable to perform the desired query
 */
int parseParams(int argc, char *argv[])
{
	if (argc == 1)
	{
		authorInfo(hgrev);
		return PARSE_EXIT;
	}

	for (int k = 1; k < argc; k++)
	{
		if (string("-d").compare(argv[k]) == 0)
			debug = true;
		else if (string("--formats").compare(argv[k]) == 0)
		{
			printArray(acceptedformats, NUM_FORMATS);
			return PARSE_EXIT;
		}
		else if (string("--problems").compare(argv[k]) == 0)
		{
			printArray(acceptedproblems, NUM_PROBLEMS);
			return PARSE_EXIT;
		}
		else if (string("--help").compare(argv[k]) == 0)
		{
			showHelp(hgrev);
			return PARSE_EXIT;
		}
		else if (string("-f").compare(argv[k]) == 0)
		{
			inputfile = string(argv[++k]);
		}
		else if (string("-a").compare(argv[k]) == 0)
		{
			argumentDecision = string(argv[++k]);
		}
		else if (string("-fo").compare(argv[k]) == 0)
		{
			if (!isInArray(string(argv[++k]), acceptedformats, NUM_FORMATS))
			{
				return PARSE_UNABLE;
			}
		}
		else if (string("-p").compare(argv[k]) == 0)
		{
			string p = string(argv[++k]);
			if (!isInArray(p, acceptedproblems, NUM_PROBLEMS))
			{
				return PARSE_UNABLE;
			}

			size_t dash = p.find("-");
			if (dash == string::npos)
			{
				return PARSE_ERROR;
			}
			problem = p.substr(0, dash);
			semantics = p.substr(dash + 1);
		}
		else if (string("--ExtEnc").compare(argv[k]) == 0)
		{
			try
			{
				global_enc = Encoding(string(argv[++k]));
			} catch (exception &e)
			{
				cout << e.what() << endl;
				return PARSE_ERROR;
			}
		}
		else if (string("--prefConf").compare(argv[k]) == 0)
		{
			try
			{
				confPreferred = ConfigurationPreferred(argv[++k]);
			} catch (exception &e)
			{
				cout << e.what() << endl;
				return PARSE_ERROR;
			}
		}
		else if (string("--stabConf").compare(argv[k]) == 0)
		{
			try
			{
				confStable = ConfigurationStable(argv[++k]);
			} catch(exception &e)
			{
				cout << e.what() << endl;
				return PARSE_ERROR;
			}

		}
		else if (string("--semistabConf").compare(argv[k]) == 0)
				{
					try
					{
						confSemiStable = ConfigurationSemiStable(argv[++k]);
					} catch(exception &e)
					{
						cout << e.what() << endl;
						return PARSE_ERROR;
					}

				}
		else if (string("--complConf").compare(argv[k]) == 0)
				{
					try
					{
						confComplete = ConfigurationComplete(argv[++k]);
					} catch(exception &e)
					{
						cout << e.what() << endl;
						return PARSE_ERROR;
					}

				}
		else if (string("--sat").compare(argv[k]) == 0)
		{
			//default
			satsolver = string(path) + "/" + defaultsolver;

			satsolver = string(argv[++k]);

			confStable = ConfigurationStable("01111");
		}
		else if (string("--minisat-var-decay").compare(argv[k]) == 0)
		{
			opt_var_decay = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-cla-decay").compare(argv[k]) == 0)
		{
			opt_clause_decay = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-rnd-freq").compare(argv[k]) == 0)
		{
			opt_random_var_freq = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-rnd-seed").compare(argv[k]) == 0)
		{
			opt_random_seed = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-ccmin-mode").compare(argv[k]) == 0)
		{
			opt_ccmin_mode = strtoll(argv[++k], NULL, 10);
		}
		else if (string("--minisat-phase-saving").compare(argv[k]) == 0)
		{
			opt_phase_saving = strtoll(argv[++k], NULL, 10);
		}
		else if (string("--minisat-rnd-init").compare(argv[k]) == 0)
		{
			if (strtoll(argv[++k], NULL, 10) == 1)
				opt_rnd_init_act = true;
			else
				opt_rnd_init_act = false;
		}
		else if (string("--minisat-luby").compare(argv[k]) == 0)
		{
			if (strtoll(argv[++k], NULL, 10) == 0)
				opt_luby_restart = false;
			else
				opt_luby_restart = true;
		}
		else if (string("--minisat-rfirst").compare(argv[k]) == 0)
		{
			opt_restart_first = strtoll(argv[++k], NULL, 10);
		}
		else if (string("--minisat-rinc").compare(argv[k]) == 0)
		{
			opt_restart_inc = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-gc-frac").compare(argv[k]) == 0)
		{
			opt_garbage_frac = strtod(argv[++k], NULL);
		}
		else if (string("--minisat-min-learnts").compare(argv[k]) == 0)
		{
			opt_min_learnts_lim = strtoll(argv[++k], NULL, 10);
		}

		//experimental
		else if (string("--minisat-rnd-pol").compare(argv[k]) == 0)
		{
			if (strtoll(argv[++k], NULL, 10) == 1)
				opt_rnd_pol = true;
			else
				opt_rnd_pol = false;
		}
		else if (string("--minisat-default-upol").compare(argv[k]) == 0)
		{
			if (strtoll(argv[++k], NULL, 10) == 1)
				opt_default_upol = true;
			else
				opt_default_upol = false;

		}



		else
		{
			cout << "Unrecognised parameter: " << argv[k] << endl;
			return PARSE_ERROR;
		}
	}
	return true;
}

void authorInfo(const char *rev)
{
	cout << "ArgSemSAT " << rev << endl;
	cout << "Federico Cerutti <federico.cerutti@acm.org>" << endl;
	cout << "Mauro Vallati <mauro.vallati@hud.ac.uk>" << endl;
	cout << "Massimiliano Giacomin <massimiliano.giacomin@unibs.it>" << endl;
	cout << "Tobia Zanetti <t.zanetti001@studenti.unibs.it>" << endl;

}

/**
 * @brief			Function for printing on screen a disclaimer and a brief help
 * @param[in] rev	The version of this software
 * @retval	void
 */
void showHelp(const char *rev)
{
	cout << rev << endl;

	cout << "ArgSemSAT Copyright (C) 2012-2017" << endl
			<< "Federico Cerutti <federico.cerutti@acm.org>" << endl
			<< "Mauro Vallati <m.vallati@hud.ac.uk>" << endl
			<< "Massimiliano Giacomin <massimiliano.giacomin@unibs.it>" << endl
			<< "Tobia Zanetti <t.zanetti001@studenti.unibs.it>" << endl
			<< endl;
	cout << "This program comes with ABSOLUTELY NO WARRANTY" << endl;
	cout << "This is free software, under the MIT license" << endl;

	cout << "#### Running" << endl;
	cout << "./ArgSemSAT <param1> ... <paramN>" << endl;
	cout << "--help\t\t\t this help" << endl;
	cout << "-d \t\t\t *HIGH* level of debug (very slow, very dense output)"
			<< endl;
	cout << "-f <filename>\t\t input file name for a problem" << endl;
	cout << "-fo <format>\t\t format of the input file" << endl;
	cout << "-p <problem>\t\t problem to be solved" << endl;
	cout << "-a <additional>\t\t argument to check the acceptance" << endl;
	cout << "--formats\t\t list of supported file types" << endl;
	cout << "--problems\t\t list of supported problems" << endl;
	cout
			<< "--ExtEnc <CIr><CIl><COr><COl><CUr><CUl> sequence of 6 booleans without spaces: by default 101010"
			<< endl;
	cout << "--sat\t\t\t SAT solver full path: by default internal MINISAT" << endl; // << path << "/"
			//<< defaultsolver << endl;
	cout
			<< "--prefConf <IntIN><IntOUT><ExtIN><ExtOUT><Stable><ImprovedVersion> sequence of 6 booleans without spaces: by default 111100. This configuration is used for the EE task, skipping the last boolean. When DS task is considered, if <ImprovedAlgorithm>=1 a new algorithm for the calculation is used, <Stable> is skipped, and the other booleans maintain their meaning"
			<< endl;
	cout << "--stabConf <AllSAT><IN><OUT><DC Impr><DS Impr> sequence of 5 booleans without spaces: by default 10011 unless an external sat solver is selected, in that case is 01111. If <AllSAT>=1, the other two booleans will be ignored unless it is used in conjunction to EE-PR" << endl;
	cout << "--semistabConf <AllSAT><OldVersion> sequence of 2 booleans without spaces: by default 00. If <OldVersion>=1, the other boolean will be ignored" << endl;
	cout << "--complConf <AllSAT> 1 boolean: by default 0." << endl;


	cout << "--minisat-var-decay\t The variable activity decay factor, between 0 and 1 (default 0.95)" << endl;
	cout << "--minisat-cla-decay\t The clause activity decay factor, between 0 and 1 (default 0.999)" << endl;
	cout << "--minisat-rnd-freq\t The frequency with which the decision heuristic tries to choose a random variable, between 0 andh 1 (default 0)" << endl;
	cout << "--minisat-rnd-seed\t Used by the random variable selection, double (default 91648253)" << endl;
	cout << "--minisat-ccmin-mode\t Controls conflict clause minimization (0=none, 1=basic, 2=deep), default 2" << endl;
	cout << "--minisat-phase-saving\t Controls the level of phase saving (0=none, 1=limited, 2=full), default 2" << endl;
	cout << "--minisat-rnd-init\t Randomize the initial activity, 0 or 1 (default 0)" << endl;
	cout << "--minisat-luby\t Use the Luby restart sequence, 0 or 1 (default 1)" << endl;
	cout << "--minisat-rfirst\t The base restart interval, integer (default 100)" << endl;
	cout << "--minisat-rinc\t Restart interval increase factor, double (default 2)" << endl;
	cout << "--minisat-gc-frac\t The fraction of wasted memory allowed before a garbage collection is triggered, between 0 and 1 (default 0.2)" << endl;
	cout << "--minisat-min-learnts\t Minimum learnt clause limit, integer (default 0)" << endl;
	cout << "--minisat-rnd-pol\t EXPERIMENTAL Randomised user polarities, 0 or 1 (default 0)" << endl;
	cout << "--minisat-default-upol\t EXPERIMENTAL Default user polarity, 0 or 1 (default 0)" << endl;
	return;
}

bool parse_solution_aspartix(set<set<string> > *preferred, const char *file)
{
	ifstream infile;
	infile.open(file);
	if (infile.good() == false)
		return false;

	string inLine;
	while (getline(infile, inLine))
	{
		int start = 0;
		int pos = 0;
		set<string> sol_asp = set<string>();

		while (((int) (pos = inLine.find("in(", start))) != ((int) string::npos))
		{
			string arg = inLine.substr(pos + 3,
					inLine.find(")", pos + 3) - (pos + 3));
			sol_asp.insert(arg);
			start = pos + 4;
		}
		(*preferred).insert(sol_asp);
	}
	set<set<string> >::iterator it;
	for (it = preferred->begin(); it != preferred->end(); it++)
	{
		set<string>::iterator inner;
		cout << "{";
		for (inner = (*it).begin(); inner != (*it).end(); inner++)
		{
			cout << (*inner) << " ";
		}
		cout << "}" << endl;
	}
	return true;
}
