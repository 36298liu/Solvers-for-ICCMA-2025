/*
 * NaiveAllSATSolver.h
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#ifndef NAIVEALLSATSOLVER_H_
#define NAIVEALLSATSOLVER_H_

#include "AllSATSolver.h"

namespace Allsat {
/**
 * This class would generate blocking clauses that would have all assignments
 */
class NaiveAllSATSolver: public AllSATSolver {
private:
	Minisat::vec<Minisat::Lit> _clauseCache;
	Minisat::vec<Minisat::Lit> _solutionCubeCache;
	Minisat::vec<Minisat::CRef> _dummy;

public:
	NaiveAllSATSolver(AccessSolver * solver);
	virtual ~NaiveAllSATSolver();
	virtual const Minisat::vec<Minisat::CRef>& getCoveredClauses();
	virtual const Minisat::vec<Minisat::Lit>& generateBlockingClause(Minisat::vec<Minisat::Lit> & solutionCube);

};


}
#endif /* NAIVEALLSATSOLVER_H_ */
