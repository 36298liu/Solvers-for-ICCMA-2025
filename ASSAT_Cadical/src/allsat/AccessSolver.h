/*
 * AccessSolver.h
 *
 *  Created on: Mar 9, 2013
 *      Author: yinlei
 */

#ifndef ACCESSSOLVER_H_
#define ACCESSSOLVER_H_

#include "core/Solver.h"
#include <vector>


namespace Allsat {

class AccessSolver: public Minisat::Solver {
public:
	Minisat::Clause & clause (Minisat::CRef cr) {return this->ca[cr];}
	const Minisat::Clause & clause (Minisat::CRef cr) const {return this -> ca[cr];}
	const Minisat::vec<Minisat::CRef>& origClauses() { return this -> clauses;}
	const Minisat::vec<Minisat::CRef>& learntClauses() {return this->learnts;}
	void backtrack(int i) {this->cancelUntil(i);}
	Minisat::lbool solveCustom() {return this-> solve_();}
	Minisat::CRef antecedentClause(Minisat::Var v) {return this -> reason(v);}
	int decisionLevel(Minisat::Var v) {return this -> level(v);}
	bool isDecision(Minisat::Var v) {return antecedentClause(v) == Minisat::CRef_Undef;}

	virtual bool addOrigClause(Minisat::vec<Minisat::Lit> & ps);

	std::vector<Minisat::Lit> _singleLits;
};

} /* namespace Allsat */
#endif /* ACCESSSOLVER_H_ */
