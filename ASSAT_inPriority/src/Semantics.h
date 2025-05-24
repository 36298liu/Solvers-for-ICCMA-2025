/**
 * @file 		Semantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */


#ifndef SEMANTICS_H_
#define SEMANTICS_H_

#include <ConfigurationStable.h>
#include "AF.h"
#include "Labelling.h"
#include "SATFormulae.h"
#include "Encoding.h"
#include <vector>
#include <iostream>
#include <sstream>

#include <exception>


class SolverException: public exception
{
	virtual const char* what() const throw ()
	{
		return "The NP Oracle could not terminate properly";
	}
};

extern bool debug;
using namespace std;

extern int (*SatSolver)(stringstream *, int, int, vector<int> *);

class Semantics
{
protected:
	AF *af; //!< @brief The Argumentation Framework considered
	Encoding encoding; //!< @brief The chosen encoding @see Semantics#Semantics
	SATFormulae sat_pigreek; //!< @brief The Sat Formulae as described in TAFA-13 filled in by the constructor Semantics#Semantics
	vector<Labelling> labellings; //!<@brief Attribute that contains the computed extensions
	int complete_labelling_SAT_constraints();
	bool satlab(SATFormulae, Labelling *, bool results=true);
	bool allsat(SATFormulae sat, vector<Labelling> *lab, vector<OrClause> *, ConfigurationStable *, int);
	void cleanlabs();
	void add_non_emptiness();
	bool credulousAcceptance(Argument *);
public:
	typedef vector<Labelling>::const_iterator iterator;
	Semantics(AF *, Encoding);
	virtual ~Semantics();
	iterator begin() const;
	iterator end() const;
	string toString() const;
	vector<Labelling> getLabellings();

};

ostream& operator<<(ostream& , const Semantics& );


#endif /* SEMANTICS_H_ */
