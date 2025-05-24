/*
 * AllClauseAllSATSolver.h
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#ifndef ALLCLAUSEALLSATSOLVER_H_
#define ALLCLAUSEALLSATSOLVER_H_

#include "SmartAllSATSolver.h"

namespace Allsat {

class AllClauseAllSATSolver: public SmartAllSATSolver {
public:
	AllClauseAllSATSolver(AccessSolver *solver, bool useDecisionOnlyBlockingClause, ClauseSelectionT type = GREEDYSLOW);
	virtual ~AllClauseAllSATSolver();
	virtual const Minisat::vec<Minisat::CRef> & getCoveredClauses();
	virtual void updateStateUponSAT(); //generate (regenerate) a list of clauses that each variable satisfies

private:
	Minisat::vec<Minisat::CRef> _allClauseRefTemp;
	int _lastSATCount;
};

} /* namespace Allsat */
#endif /* ALLCLAUSEALLSATSOLVER_H_ */
