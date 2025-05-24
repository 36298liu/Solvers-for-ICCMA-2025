/**
 * @file 		SATFormulae.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef SATFORMULAE_H_
#define SATFORMULAE_H_

#include <vector>
#include <string>
#include <sstream>
#include <cstdarg>
#include "OrClause.h"
#include "Argument.h"
using namespace std;

class SATFormulae {
	vector<OrClause> clauses_and;
	long numvar;
public:
	SATFormulae(long);
	SATFormulae();
	void setNumVar(long);
	void appendOrClause(OrClause);
	void toSS(stringstream *) const;
	void clone(SATFormulae *);
	int size() const;
	virtual ~SATFormulae();
	bool empty();
	string toString() const;
	long getNumVar() const;
	void merge(SATFormulae *);
};
ostream& operator<<(ostream& , const SATFormulae& );

#endif /* SATFORMULAE_H_ */
