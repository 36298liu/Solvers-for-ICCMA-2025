/*
 * NaiveAllSATSolver.cpp
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#include "NaiveAllSATSolver.h"
using namespace Minisat;
namespace Allsat {
    NaiveAllSATSolver::NaiveAllSATSolver(AccessSolver *solver) :
	    AllSATSolver(solver)
    {
    }

    NaiveAllSATSolver::~NaiveAllSATSolver()
    {
    }
    /**
     * NaiveAllSAT does not require to have a clause list, so we do not return anything here
     */
    const vec<CRef> & NaiveAllSATSolver::getCoveredClauses()
    {
	return _dummy;
    }

    const vec<Lit> & NaiveAllSATSolver::generateBlockingClause(vec<Lit> & solutionCube)
    {
	const vec<lbool> & model = this->getModel();
	_clauseCache.clear(false);
	for (int i = 0; i < model.size(); ++i) {
	    if (model[i] != l_Undef) {
		_clauseCache.push(toLit(i + i + (model[i] == l_False? 0: 1)));
	    }
	}
	return _clauseCache;
    }

}
