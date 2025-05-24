/**
 * @file 		ArgSemSAT.cpp
 * @brief 		Main file
 * @author 		Federico Cerutti <federico.cerutti@acm.org> and
 * 				Mauro Vallati <m.vallati@hud.ac.uk>
 * @copyright	MIT
 */

#include "argsemsat.h"
#include <unistd.h>
#include <libgen.h>
#include <ctime>


/**
 * @brief Configuration variables
 */
bool debug = false;
bool externalsat = true;
string satsolver = "";
//string defaultsolver = "satsolver -model";
string defaultsolver = "";
bool manualopt = false;
string inputfile;
string semantics;
string problem;
Encoding global_enc("101010");
ConfigurationPreferred confPreferred("111101");
ConfigurationStable confStable("10011");
ConfigurationSemiStable confSemiStable("00");
ConfigurationComplete confComplete("1");
string path;
string argumentDecision;

int (*SatSolver)(stringstream *, int, int, vector<int> *) = NULL;

//time_t start;

#ifndef UNIT_TEST

void printbooleanprobo(bool res)
{
	if (res)
		cout << "YES" << endl;
	else
		cout << "NO" << endl;
}

/**
 * @brief 	Main
 * @retval int	The return value can be:
 * 				* `-127`: Missing parameters
 * 				* `-1`: Unable to parse the AF file
 * 				* `-126`: Something goes wrong
 * 				* `-125`: Wrong SAT Solver
 * 				* `0`: SUCCESS!!!
 *
 */
int main(int argc, char *argv[])
{
	char buf[2048];
	readlink("/proc/self/exe", buf, 2047);
	path = string(dirname(buf));

	//time(&start);

	int p = parseParams(argc, argv);

	if (p == PARSE_EXIT)
	{
		return 0;
	}
	if (p == PARSE_ERROR || p == PARSE_UNABLE)
	{
		showHelp(hgrev);
		return -127;
	}

	AF framework = AF();
	if (!framework.readFile(inputfile))
	{
		cerr << "Either missing file or parsing error " << endl;

		showHelp(hgrev);
		return -1;
	}

	if (semantics.compare(complete_string_const) == 0)
	{
		CompleteSemantics comp = CompleteSemantics(&framework, global_enc,
				&confComplete);
		if (problem.compare(enumerateall) == 0)
		{
			comp.compute();
			cout << comp << endl;
		}
		else if (problem.compare(credulous) == 0)
		{
			printbooleanprobo(
					comp.credulousAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(skeptical) == 0)
		{
			printbooleanprobo(
					comp.skepticalAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			cout << (*(comp.someExtension())) << endl;
		}

	}
	else if (semantics.compare(preferred_string_const) == 0)
	{

		/*global_enc = Encoding("101010");
		confComplete = ConfigurationComplete("1");
		opt_ccmin_mode = strtoll("2", NULL, 10);
		opt_clause_decay = strtod("0.999", NULL);
		opt_default_upol = false;
		opt_garbage_frac = strtod("0.2", NULL);
		opt_luby_restart = false;
		opt_min_learnts_lim = strtoll("490.25755704389815", NULL, 10);
		opt_phase_saving = strtoll("0", NULL, 10);
		opt_restart_first = strtoll("100.0", NULL, 10);
		opt_restart_inc = strtod("1.5017109340581025", NULL);
		opt_random_var_freq = strtod("0.03126143827806218", NULL);
		opt_rnd_init_act = false;
		opt_rnd_pol = false;
		opt_var_decay = strtod("0.9987704171663054", NULL);
		confPreferred = ConfigurationPreferred("111110");
		confSemiStable = ConfigurationSemiStable("10");
		confStable = ConfigurationStable("011");*/

		PreferredSemantics pref = PreferredSemantics(&framework, global_enc,
				&confPreferred, &confStable);
		if (problem.compare(enumerateall) == 0)
		{
			pref.compute();
			cout << pref << endl;
		}
		else if (problem.compare(credulous) == 0)
		{
			printbooleanprobo(
					pref.credulousAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(skeptical) == 0)
		{
			printbooleanprobo(
					pref.skepticalAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			cout << (*(pref.someExtension())) << endl;
		}
	}
	else if (semantics.compare(grounded_string_const) == 0)
	{
		/*global_enc = Encoding("111100");
		confComplete = ConfigurationComplete("1");
		opt_ccmin_mode = strtoll("1", NULL, 10);
		opt_clause_decay = strtod("0.23390174759549986 ", NULL);
		opt_default_upol = true;
		opt_garbage_frac = strtod("0.20601142379198223", NULL);
		opt_luby_restart = false;
		opt_min_learnts_lim = strtoll("730.4823518397477", NULL, 10);
		opt_phase_saving = strtoll("0", NULL, 10);
		opt_restart_first = strtoll("8.738052547018649", NULL, 10);
		opt_restart_inc = strtod("3.125937942373136", NULL);
		opt_random_var_freq = strtod("5.278042576936093E-4", NULL);
		opt_rnd_init_act = true;
		opt_rnd_pol = false;
		opt_var_decay = strtod("0.4411787211246362 ", NULL);
		confPreferred = ConfigurationPreferred("111110");
		confSemiStable = ConfigurationSemiStable("11");
		confStable = ConfigurationStable("001");*/

		GroundedSemantics ground = GroundedSemantics(&framework, global_enc);
		if (problem.compare(enumerateall) == 0)
		{
			ground.compute();
			cout << ground << endl;
		}
		else if (problem.compare(credulous) == 0)
		{
			printbooleanprobo(
					ground.credulousAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(skeptical) == 0)
		{
			printbooleanprobo(
					ground.skepticalAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			cout << (*(ground.someExtension())) << endl;
		}
	}
	else if (semantics.compare(stable_string_const) == 0)
	{
		/*global_enc = Encoding("010101");
		confComplete = ConfigurationComplete("0");
		opt_ccmin_mode = strtoll("1", NULL, 10);
		opt_clause_decay = strtod("0.961034697755705", NULL);
		opt_default_upol = true;
		opt_garbage_frac = strtod("0.545570241749875", NULL);
		opt_luby_restart = true;
		opt_min_learnts_lim = strtoll("924.2659301324894", NULL, 10);
		opt_phase_saving = strtoll("0", NULL, 10);
		opt_restart_first = strtoll("615.888219555366", NULL, 10);
		opt_restart_inc = strtod("3.934939123294029", NULL);
		opt_random_var_freq = strtod("0.14230182176061745", NULL);
		opt_rnd_init_act = false;
		opt_rnd_pol = true;
		opt_var_decay = strtod("0.0046591659539415575", NULL);
		confPreferred = ConfigurationPreferred("111110");
		confSemiStable = ConfigurationSemiStable("10");
		confStable = ConfigurationStable("100");*/

		StableSemantics stab = StableSemantics(&framework, global_enc,
				&confStable);
		if (problem.compare(enumerateall) == 0)
		{
			stab.compute();
			cout << stab << endl;
		}
		else if (problem.compare(credulous) == 0)
		{
			printbooleanprobo(
					stab.credulousAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(skeptical) == 0)
		{
			printbooleanprobo(
					stab.skepticalAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			SetArguments *ret = stab.someExtension();
			if (ret == NULL)
				printbooleanprobo(false);
			else
				cout << (*(ret)) << endl;
		}
	}
	else if (semantics.compare(semistable_string_const) == 0)
	{

		/*global_enc = Encoding("101010");
		confComplete = ConfigurationComplete("1");
		opt_ccmin_mode = strtoll("2", NULL, 10);
		opt_clause_decay = strtod("0.999", NULL);
		opt_default_upol = true;
		opt_garbage_frac = strtod("0.06246418299614409", NULL);
		opt_luby_restart = true;
		opt_min_learnts_lim = strtoll("0.0", NULL, 10);
		opt_phase_saving = strtoll("0", NULL, 10);
		opt_restart_first = strtoll("100.0", NULL, 10);
		opt_restart_inc = strtod("4.273630441792707", NULL);
		opt_random_var_freq = strtod("0.0", NULL);
		opt_rnd_init_act = true;
		opt_rnd_pol = false;
		opt_var_decay = strtod("0.95", NULL);
		confPreferred = ConfigurationPreferred("111110");
		confSemiStable = ConfigurationSemiStable("10");
		confStable = ConfigurationStable("011");*/

		SemistableSemantics semistab = SemistableSemantics(&framework,
				global_enc, &confStable, &confSemiStable);
		if (problem.compare(enumerateall) == 0)
		{
			semistab.compute();
			cout << semistab << endl;

			// Time spent by AllSat
			//printf("%.2f\n", semistab.getTimeAllSat());
			//Time spent by the internal do-while loop
			//printf("%.2f\n", semistab.getTimeInternalDoWhile());
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			SetArguments *ret = semistab.someExtension();
			if (ret == NULL)
				printbooleanprobo(false);
			else
				cout << (*(ret)) << endl;
		}
		else if (problem.compare(skeptical) == 0)
		{
			printbooleanprobo(
					semistab.skepticalAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
		else if (problem.compare(credulous) == 0)
		{
			printbooleanprobo(
					semistab.credulousAcceptance(
							framework.getArgumentByName(argumentDecision)));
		}
	}


	return 0;
}
#endif
