/*
 * SmartBlockingAllSATSolver.cc
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#include "SmartBlockingAllSATSolver.h"

using namespace Minisat;
using namespace std;
namespace Allsat {

SmartBlockingAllSATSolver::SmartBlockingAllSATSolver(AccessSolver * solver, bool useDecisionOnlyBlockingClause, ClauseSelectionT type) :
		SmartAllSATSolver(solver, useDecisionOnlyBlockingClause, type), _watchListInitialized(false),_origClauseCount(-1)
{}

SmartBlockingAllSATSolver::~SmartBlockingAllSATSolver() {
}

//we only do it once here, as it's the FIRST time, we do not have any blocking clauses
//that would pollute the clause list
const Minisat::vec<Minisat::CRef>& SmartBlockingAllSATSolver::getCoveredClauses() {
    if (_origClauseCount == -1) {
	_origClauseCount = _pSolver -> origClauses().size();
	_origClauseVec.growTo(_origClauseCount);
    }

    const vec<CRef> & cls = _pSolver -> origClauses();
    assert(cls.size() >= _origClauseCount);
    for (int i=0;i<_origClauseCount;++i) {
	_origClauseVec[i] = cls[i];
	assert(!_pSolver->clause(cls[i]).learnt());
    }

    if (_pSolver -> verbosity > 1) {
        cout << "origClauses().size=" << cls.size() << endl;
    }
    return _origClauseVec;
}

//generate (regenerate) a list of clauses that each variable satisfies
void SmartBlockingAllSATSolver::updateStateUponSAT()
{
 //   copyModel();
//    if (!_watchListInitialized) {
	//we only do it once here, as it's the FIRST time, we do not have any blocking clauses
	//that would pollute the clause list
    //that actually doesn't work, we have to initialize every time.
//    const vec<CRef> & clauses = getCoveredClauses();
//	for (vector<BlockingVariable>::iterator itr = _blockingVars.begin();
//		itr != _blockingVars.end(); ++ itr) {
//	    (*itr).coveredClauses[0].clear();
//	    (*itr).coveredClauses[0].reserve(10);
//	    (*itr).coveredClauses[1].clear();
//	    (*itr).coveredClauses[1].reserve(10);
//	}
//	for (int i = 0; i < clauses.size(); ++ i) {
//	    const Clause & cl = _pSolver -> clause(clauses[i]);
//	    int numLits = cl.size();
//	    for (int loc = 0; loc < numLits; ++ loc) {
//		Lit l = cl[loc];
//		_blockingVars[var(l)].coveredClauses[sign(l)].push_back(i);
//	    }
//	}
////	_watchListInitialized = true;
//    }
    const vec<CRef> & clauses = getCoveredClauses();
    for (auto itr = _blockingVars.begin(); itr != _blockingVars.end(); ++itr) {
	(*itr).coveredClauses[0].clear();
	(*itr).coveredClauses[1].clear();
    }

    if (_pSolver -> verbosity > 1) cout << "# of clauses: "<< clauses.size() << endl;

    for (int i = 0; i < clauses.size(); ++i) {
	Clause & cl = _pSolver->clause(clauses[i]);
        if (_pSolver -> verbosity > 1) {
            cout << "Clause (" << i<< "): " << cl << endl;
        }

	int numLits = cl.size();
	for (int loc = 0; loc < numLits; ++loc) {
	    Lit l = cl[loc];
	    BlockingVariable & bv = _blockingVars[var(l)];
	    if ((_pSolver->modelValue(l)) == l_True) {
		bv.coveredClauses[sign(l)].push_back(clauses[i]);
		if (_pSolver -> verbosity > 1) {
		        cout << "Clause ("<<clauses[i] <<")";
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
