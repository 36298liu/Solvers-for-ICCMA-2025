/*
 * AllClauseAllSATSolver.cc
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#include "AllClauseAllSATSolver.h"
#include <vector>
using namespace std;
using namespace Minisat;

namespace Allsat {

AllClauseAllSATSolver::AllClauseAllSATSolver(AccessSolver *solver,bool useDecisionOnlyBlockingClause,
        ClauseSelectionT type) :
	SmartAllSATSolver(solver, useDecisionOnlyBlockingClause, type),_lastSATCount(-1)
{
}

AllClauseAllSATSolver::~AllClauseAllSATSolver()
{
}

const vec<CRef>& AllClauseAllSATSolver::getCoveredClauses()
{
    //we only need to generate covered clauses ONCE
    if (_lastSATCount != _stats.numSATs) {
	this->_allClauseRefTemp.clear(false);
	this->_allClauseRefTemp.capacity(
	        _pSolver->nClauses() + _pSolver->learntClauses().size());
	_pSolver->origClauses().copyTo(this->_allClauseRefTemp);
	int origSize = this->_allClauseRefTemp.size();
	int learntSize = _pSolver->learntClauses().size();
//	this->_allClauseRefTemp.growTo(origSize + learntSize);
//	for (int i = 0; i < learntSize; ++i) {
//	    this->_allClauseRefTemp[origSize + i] =
//		    _pSolver->learntClauses()[i];
//	}
    }
    return this->_allClauseRefTemp;
}


//for all clause variety, we need to update coveredClauses every time as the list is not constant
void AllClauseAllSATSolver::updateStateUponSAT()
{
    const vec<CRef> & clauses = getCoveredClauses();
    for (vector<BlockingVariable>::iterator itr = _blockingVars.begin();
	    itr != _blockingVars.end(); ++itr) {
	(*itr).coveredClauses[0].clear();
	(*itr).coveredClauses[1].clear();
    }
    for (int i = 0; i < clauses.size(); ++i) {
	Clause & cl = _pSolver->clause(clauses[i]);
	int numLits = cl.size();
	for (int loc = 0; loc < numLits; ++loc) {
	    Lit l = cl[loc];
	    BlockingVariable & bv = _blockingVars[var(l)];
	    if ((_pSolver->modelValue(l)) == l_True) {
		bv.coveredClauses[sign(l)].push_back(clauses[i]);
		if (_pSolver -> verbosity > 1) {
		        cout << "Clause  ("<<clauses[i] <<")";
			printClause(cl, cout);
			cout << " is added to variable "<< var(l) <<"'s coveredClause ["<<sign(l)<<"]"<<endl;
		}
	    }
	}
    }
    if (_pSolver->verbosity > 1) {
    for (int i = 0; i < _blockingVars.size(); ++i) {
	for (int n = 0; n < 2; ++ n) {
	    cout << "Variable "<<i<<".coveredClause["<<n<<"]:";
	    for (auto itr = _blockingVars[i].coveredClauses[n].begin();
		    itr !=  _blockingVars[i].coveredClauses[n].end(); ++ itr) {
		cout << " "<< (*itr);
	    }
	    cout << endl;
	}
    }
    }
}

} /* namespace Allsat */
