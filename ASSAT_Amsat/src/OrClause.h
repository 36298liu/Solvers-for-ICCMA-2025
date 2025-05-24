/**
 * @file 		OrClause.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef ORCLAUSE_H_
#define ORCLAUSE_H_

#include <vector>
#include <string>
#include <sstream>
#include <cstdarg>
#include "Argument.h"
using namespace std;

class OrClause {
	vector<Variable> clause;
public:
	OrClause();
	OrClause(int, ...);
	void appendVariable(Variable);
	void addHeadVariable(Variable);
	void toSS(stringstream *) const;
	string toString() const;
	void clone(OrClause *);
	virtual ~OrClause();
	bool isEmpty() const;
};
ostream& operator<<(ostream& , const OrClause& );

#endif /* ORCLAUSE_H_ */
