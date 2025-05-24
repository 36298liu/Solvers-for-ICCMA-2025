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
#include <filesystem>
#include <fstream>
#include <sys/stat.h>  // 确保包含这个头文件
#include <cerrno>      // 用于错误处理

using namespace std;
// namespace fs = std::filesystem;
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
ConfigurationComplete confComplete("0");//默认为1
string path;
string argumentDecision;

int (*SatSolver)(stringstream *, int, int, vector<int> *) = NULL;

time_t start;
clock_t starta,end0;

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

	time(&start);
	starta=clock();

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
	
	// 记录处理时间
	std::string result_content;
	auto print_sigma_extension = [](SetArguments* ext) {
        if (ext && !ext->empty()) {
            cout << "w";
            for (SetArgumentsIterator it = ext->begin(); it != ext->end(); ++it)
                cout << " " << (*it)->getName();
            cout << endl;
        }
    };

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
			SetArguments *ret = comp.someExtension();
            if (ret && !ret->empty()) {
                print_sigma_extension(ret);
            } else {
                cout << "NO" << endl;
            }
		}

	}
	else if (semantics.compare(preferred_string_const) == 0)
	{

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
			SetArguments *ret = pref.someExtension();
            if (ret && !ret->empty()) {
                print_sigma_extension(ret);
            } else {
                cout << "NO" << endl;
            }
		}
	}
	else if (semantics.compare(grounded_string_const) == 0)
	{

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
			SetArguments *ret = ground.someExtension();
            if (ret && !ret->empty()) {
                print_sigma_extension(ret);
            } else {
                cout << "NO" << endl;
            }
		}
	}
	else if (semantics.compare(stable_string_const) == 0)
	{
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
            if (ret && !ret->empty()) {
                print_sigma_extension(ret);
            } else {
                cout << "NO" << endl;
            }
		}
	}
	else if (semantics.compare(semistable_string_const) == 0)
	{
		SemistableSemantics semistab = SemistableSemantics(&framework,
				global_enc, &confStable, &confSemiStable);
		if (problem.compare(enumerateall) == 0)
		{
			semistab.compute();
			cout << semistab << endl;
		}
		else if (problem.compare(enumeratesome) == 0)
		{
			SetArguments *ret = semistab.someExtension();
            if (ret && !ret->empty()) {
                print_sigma_extension(ret);
            } else {
                cout << "NO" << endl;
            }
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

	end0=clock();           //程序结束用时
	double endtime=(end0-starta)/CLOCKS_PER_SEC;
	return 0;
}
#endif
