/*
 * SmartBlockingAllSATSolver.h
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#ifndef SMARTBLOCKINGALLSATSOLVER_H_
#define SMARTBLOCKINGALLSATSOLVER_H_

#include "SmartAllSATSolver.h"

namespace Allsat {

class SmartBlockingAllSATSolver: public SmartAllSATSolver {
public:
    SmartBlockingAllSATSolver(AccessSolver * solver, bool useDecisionOnlyBlockingClause, ClauseSelectionT type =
	    GREEDYSLOW);
    virtual ~SmartBlockingAllSATSolver();

    virtual const Minisat::vec<Minisat::CRef> & getCoveredClauses();

    virtual void updateStateUponSAT(); //generate (regenerate) a list of clauses that each variable satisfies

private:
    bool _watchListInitialized;
    Minisat::vec<Minisat::CRef> _origClauseVec;
    int _origClauseCount;
};

} /* namespace Allsat */
#endif /* SMARTBLOCKINGALLSATSOLVER_H_ */
