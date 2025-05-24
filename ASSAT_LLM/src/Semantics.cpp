/**
 * @file 		Semantics.cpp
 * @class 		Semantics
 * @brief 		General class for a semantics for an AF
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "Semantics.h"
#include "lib_pstreams/pstream.h"

#include <iostream>
#include <iomanip>
#include <string>
#include <sstream>
#include <fstream>
#include <cstring>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
//#include <fcntl.h>
#include <errno.h>

#include <cmath>

#include <stdexcept>
#include "fastformat/fastformat.h"
#include "fastformat/inserters/to_i.hpp"
#include "fastformat/sinks/ostream.hpp"
#include "fastformat/ff.hpp"

#define PSTREAMS_VERSION_MAJOR PSTREAMS_VERSION & 0xff00
#define PSTREAMS_VERSION_MINOR PSTREAMS_VERSION & 0x00f0
#define PSTREAMS_VERSION_PATCHLEVEL PSTREAMS_VERSION & 0x000f

#ifndef SLEEP_TIME
// increase these if your OS takes a while for processes to exit
# if defined (__sun) || defined(__APPLE__)
#  define SLEEP_TIME 2
# else
#  define SLEEP_TIME 1
# endif
#endif

using namespace std;
using namespace redi;

#if 0
// specialise basic_pstreambuf<char>::sync() to add a delay, allowing
// terminated processes to finish exiting, making it easier to detect
// possible writes to closed pipes (which would raise SIGPIPE and exit).
template <>
int
basic_pstreambuf<char>::sync()
{
	std::cout.flush();  // makes terminated process clean up faster.
	sleep(SLEEP_TIME+3);
	std::cout.flush();// makes terminated process clean up faster.
	return !exited() && empty_buffer() ? 0 : -1;
}
#endif

// explicit instantiations of template classes
template class redi::basic_pstreambuf<char>;
template class redi::pstream_common<char>;
template class redi::basic_ipstream<char>;
template class redi::basic_opstream<char>;
template class redi::basic_pstream<char>;
template class redi::basic_rpstream<char>;

extern string satsolver;

//bool fexists(const char *filename);

/**
 * @brief Clean the labellings
 */
void Semantics::cleanlabs()
{
	while (!this->labellings.empty())
		this->labellings.pop_back();
}

void Semantics::add_non_emptiness()
{
	OrClause noempty_clause = OrClause();
	SetArgumentsIterator it_args;
	for (it_args = af->begin(); it_args != af->end(); it_args++)
	{
		noempty_clause.appendVariable((*it_args)->InVar());
	}
	this->sat_pigreek.appendOrClause(noempty_clause);
}

bool Semantics::credulousAcceptance(Argument *arg)
{
	this->cleanlabs();
	SATFormulae compute = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&compute);
	compute.appendOrClause(OrClause(1, arg->InVar()));
	Labelling res = Labelling();
	return this->satlab(compute, &res, false);
}

/**
 * @brief Method for filling in the attribute sat_pigreek
 * @details Called by the constructor Semantics#Semantics
 */
int Semantics::complete_labelling_SAT_constraints()
{
	SetArgumentsIterator it_args;
	SetArgumentsIterator it_pred;
	for (it_args = af->begin(); it_args != af->end(); it_args++)
	{
		SetArguments *pred = (*it_args)->get_attackers();

		if (debug)
		{
			cout << "predecessors of " << (*it_args)->getName() << ": ";

			for (it_pred = pred->begin(); it_pred != pred->end(); it_pred++)
				cout << (*it_pred)->getName() << " ";
			cout << endl;

		}

		if (pred->empty())
		{
			//c2：初始争议标记为IN
			this->sat_pigreek.appendOrClause(OrClause(1, (*it_args)->InVar()));

			this->sat_pigreek.appendOrClause(
					OrClause(1, (*it_args)->NotOutVar()));

			this->sat_pigreek.appendOrClause(
					OrClause(1, (*it_args)->NotUndecVar()));
		}
		else
		{
			OrClause c3_last_clause = OrClause();
			OrClause c6_last_clause = OrClause();
			OrClause c8_or_undec_clause = OrClause();
			OrClause c7_bigor_clause = OrClause();
			//c1：标签的唯一性
			{
				this->sat_pigreek.appendOrClause(
						OrClause(3, (*it_args)->InVar(), (*it_args)->OutVar(),
								(*it_args)->UndecVar()));

				this->sat_pigreek.appendOrClause(
						OrClause(2, (*it_args)->NotInVar(),
								(*it_args)->NotOutVar()));

				this->sat_pigreek.appendOrClause(
						OrClause(2, (*it_args)->NotInVar(),
								(*it_args)->NotUndecVar()));

				this->sat_pigreek.appendOrClause(
						OrClause(2, (*it_args)->NotOutVar(),
								(*it_args)->NotUndecVar()));
			}

			// cycle among the predecessors of the node
			for (it_pred = pred->begin(); it_pred != pred->end(); it_pred++)
			{
				//c4：IN的合法约束
				if (encoding.get_C_in_right())
				{
					this->sat_pigreek.appendOrClause(
							OrClause(2, (*it_args)->NotInVar(),
									(*it_pred)->OutVar()));
				}

				//c3-last
				if (encoding.get_C_in_left())
				{
					c3_last_clause.appendVariable((*it_pred)->NotOutVar());
				}

				//c5
				if (encoding.get_C_out_left())
				{
					this->sat_pigreek.appendOrClause(
							OrClause(2, (*it_pred)->NotInVar(),
									(*it_args)->OutVar()));
				}

				//c6-last：out必须被in攻击
				if (encoding.get_C_out_right())
				{
					c6_last_clause.appendVariable((*it_pred)->InVar());
				}

				//c8-part：undec不能被in攻击
				if (encoding.get_C_undec_right())
				{
					this->sat_pigreek.appendOrClause(
							OrClause(2, (*it_args)->NotUndecVar(),
									(*it_pred)->NotInVar()));

					c8_or_undec_clause.appendVariable((*it_pred)->UndecVar());
				}

				//c7-end
				if (encoding.get_C_undec_left())
				{
					c7_bigor_clause.appendVariable((*it_pred)->InVar());
				}
			} // end cycle among the predecessors of the node

			//c3-last
			if (encoding.get_C_in_left())
			{
				c3_last_clause.appendVariable((*it_args)->InVar());
				this->sat_pigreek.appendOrClause(c3_last_clause);
			}

			//c6-last
			if (encoding.get_C_out_right())
			{
				c6_last_clause.appendVariable((*it_args)->NotOutVar());
				this->sat_pigreek.appendOrClause(c6_last_clause);
			}

			//c8
			if (encoding.get_C_undec_right())
			{
				c8_or_undec_clause.appendVariable((*it_args)->NotUndecVar());
				this->sat_pigreek.appendOrClause(c8_or_undec_clause);
			}

			//c7
			if (encoding.get_C_undec_left())
			{
				for (it_pred = pred->begin(); it_pred != pred->end(); it_pred++)
				{
					OrClause to_add = OrClause();
					c7_bigor_clause.clone(&to_add);
					to_add.appendVariable((*it_pred)->NotUndecVar());
					to_add.appendVariable((*it_args)->UndecVar());
					this->sat_pigreek.appendOrClause(to_add);
				}
			}

		}
	}

	return this->sat_pigreek.size();
}

extern int allsatlib(char *, std::vector<std::vector<int> *> *,
		std::vector<std::vector<int> *> *);
/*
 * allInOut 0 -> no check on the block clauses
 * allInOut 1 -> only positive In
 * allInOut 2 -> only positivet Out
 */
bool Semantics::allsat(SATFormulae sat, vector<Labelling> *labs,
		vector<OrClause> *blocks, ConfigurationStable *blockConf, int numArgs)
{
	int retsat = 0; //neither sat nor unsat by default
	vector<vector<int> *> models;

	vector<vector<int> *> blocking;

	if (debug)
	{
		cerr << sat.toString() << endl;
	}
	string satstring = sat.toString();

	if (blocks == NULL)
	{
		retsat = allsatlib(&satstring[0], &models, NULL);
	}
	else
	{
		retsat = allsatlib(&satstring[0], &models, &blocking);
	}

	if (debug)
	{
		cout << retsat << endl;

		for (vector<vector<int> *>::iterator m = models.begin();
				m != models.end(); m++)
		{
			for (vector<int>::iterator v = (*m)->begin(); v != (*m)->end(); v++)
			{
				cout << *v << " ";
			}
			cout << endl;
		}
	}

	if (retsat != 20 && retsat != 10)
	{
		throw SolverException();
	}

	if (retsat == 10)
	{
		for (vector<vector<int> *>::iterator lastcompfound = models.begin();
				lastcompfound != models.end(); lastcompfound++)
		{
			Labelling lab;
			//change
			for (int i = 1; i < af->numArgs()+1; i++)
			{
				if ((*lastcompfound)->at(i) > 0)
				{
					lab.add_label(af->getArgumentByNumber(i),
							Labelling::lab_in);
					if (debug)
					{
						cout << af->getArgumentByNumber(i)->getName() << endl;
					}
					continue;
				}
				if ((*lastcompfound)->at(i + af->numArgs()) > 0)
				{
					lab.add_label(af->getArgumentByNumber(i),
							Labelling::lab_out);
					continue;
				}
				if ((*lastcompfound)->at(i + 2 * af->numArgs()) > 0)
				{
					lab.add_label(af->getArgumentByNumber(i),
							Labelling::lab_undec);
					continue;
				}
			}

			labs->push_back(lab);

		}

		if (blocks != NULL)
		{
			for (vector<vector<int> *>::iterator lastblock = blocking.begin();
					lastblock != blocking.end(); lastblock++)
			{
				OrClause orBlock;
				for (vector<int>::iterator v = (*lastblock)->begin();
						v != (*lastblock)->end(); v++)
				{

					if (blockConf == NULL
							|| (blockConf->isIn() && (abs(*v) <= numArgs)
									&& (*v > 0))
							|| (blockConf->isOut() && (abs(*v) > numArgs)
									&& (abs(*v) <= 2 * numArgs) && (*v > 0)))
					{
						orBlock.appendVariable(*v);
					}
				}
				blocks->push_back(orBlock);
			}
		}
		return true;
	}
	return false;

}

extern int minisatlib(char *in, std::vector<int> *sol);

/**
 * @brief Method for deriving a labelling from a SAT Formulae
 * @details	This method is a wrapper for a SAT Solver
 * @param[in] sat	The SATFormulae as input
 * @param[out] sat	The computed Labelling
 * @retval bool `true` if a solution is found, `false` otherwise
 */
bool Semantics::satlab(SATFormulae sat, Labelling *lab, bool results)
{
	int retsat = 0; //neither sat nor unsat by default
	vector<int> lastcompfound = vector<int>();

	if (satsolver.empty())
	{
		if (debug)
		{
			cerr << sat.toString() << endl;
		}
		string satstring = sat.toString();
		retsat = minisatlib(&satstring[0], &lastcompfound);
	}
	else
	{
		const pstreams::pmode all3streams = pstreams::pstdin | pstreams::pstdout
				| pstreams::pstderr;

		pstream ps;
		ps.open(satsolver, all3streams);

		if (debug)
		{
			cerr << sat << endl;
		}

		ps << sat.toString() << peof;

		string buf;
		while (getline(ps.out(), buf))
		{
			if (buf.empty())
				continue;

			if (buf.at(0) == 'c')
				continue;

			if (buf.at(0) == 's')
			{
				if (buf.find("UNSAT") != string::npos)
				{
					retsat = 20; //unsat
					if (results == false)
						return false;
				}
				else
				{
					retsat = 10; //sat
					if (results == false)
						return true;
				}
			}

			if (buf.at(0) == 'v')
			{
				istringstream vars(buf.substr(2));
				int temp = 0;
				do
				{
					vars >> temp;
					lastcompfound.push_back(temp);
				} while (temp != 0);
			}

		}

		ps.clear();
		ps.close();

		if (retsat == 0 || (retsat == 10 && lastcompfound.empty())) // || !fexists(satsolver.c_str()))
		{
			throw runtime_error(
					"Cannot communicate with SAT or SAT error \n" + satsolver
							+ "\n" + sat.toString());
		}
	}

	/*stringstream cnf_string(stringstream::in | stringstream::out);
	 sat.toSS(&cnf_string);

	 if (debug)
	 {
	 cout << "Preparing the satsolver" << "\n";
	 cout << cnf_string.str();
	 }


	 int retsat = (*SatSolver)(&cnf_string, 3 * af->numArgs(), sat.size(),
	 &lastcompfound);*/

	if (debug)
		cout << retsat;

	if (retsat != 20 && retsat != 10)
	{
		throw SolverException();
	}

	if (retsat == 10)
	{
		//change
		//cerr<<"总数"<<af->numArgs()<<endl;
		for (int i = 0; i < af->numArgs(); i++)
		{
			if (lastcompfound.at(i) > 0)
			{
				lab->add_label(af->getArgumentByNumber(i+1), Labelling::lab_in);
				if (debug)
				{
					cout << af->getArgumentByNumber(i+1)->getName() << endl;
				}
				continue;
			}
			if (lastcompfound.at(i + af->numArgs()) > 0)
			{
				lab->add_label(af->getArgumentByNumber(i+1), Labelling::lab_out);
				continue;
			}
			if (lastcompfound.at(i + 2 * af->numArgs()) > 0)
			{
				lab->add_label(af->getArgumentByNumber(i+1),
						Labelling::lab_undec);
				continue;
			}
		}
		if (debug)
		{
			cout << "in " << lab->inargs()->cardinality() << endl;
			cout << "out " << lab->outargs()->cardinality() << endl;
			cout << "undec " << lab->undecargs()->cardinality() << endl;
		}
		return true;
	}
	return false;
}

/**
 * @brief 				Constructor for the Semantics
 * @param[in] the_af	The pointer to the object instance of `AF` which represents the argumentation
 * 						framework
 * @param[in] enc   	See Encoding#Encoding
 *
 */
Semantics::Semantics(AF *the_af, Encoding enc)
{
	this->af = the_af;
	this->labellings = vector<Labelling>();
	this->encoding = enc;
	this->sat_pigreek = SATFormulae(3 * this->af->numArgs());
	this->complete_labelling_SAT_constraints();
}

Semantics::~Semantics()
{
	// TODO Auto-generated destructor stub
}

Semantics::iterator Semantics::begin() const
{
	return this->labellings.begin();
}

Semantics::iterator Semantics::end() const
{
	return this->labellings.end();
}

std::vector<Labelling> Semantics::getLabellings()
{
	return this->labellings;
}

string Semantics::toString() const
{

	if(debug)
	{
		string ret = "[";

		Semantics::iterator it;
		for (it = this->begin(); it != this->end();)
		{
			fastformat::write(ret, "IN"+(*it).getIn().toString());
			fastformat::write(ret, "OUT"+(*it).getOut().toString());
			fastformat::write(ret, "UNDEC"+(*it).getUndec().toString());
			if (++it != this->end())
				fastformat::write(ret, ",");
		}
		fastformat::write(ret, "]");
		return ret;

	}
	string ret = "[";

	Semantics::iterator it;
	for (it = this->begin(); it != this->end();)
	{
		fastformat::write(ret, (*it).extension().toString());
		if (++it != this->end())
			fastformat::write(ret, ",");
	}
	fastformat::write(ret, "]");
	return ret;
}

ostream& operator<<(ostream& out, const Semantics& r)
{
	out << r.toString();
	return out;
}
