/*
 * SmartAllSATSolver.cc
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */
#include "mtl/Vec.h"
#include "core/Solver.h"
#include "AllSATSolver.h"
#include "SmartAllSATSolver.h"
#include <stdexcept>
#include <vector>
#include <set>
#include <stdexcept>
#include <queue>
#include <unordered_map>
#include <unordered_set>


using namespace std;
using namespace Minisat;

namespace Allsat {

SmartAllSATSolver::SmartAllSATSolver(AccessSolver * solver, bool useDecisionOnlyBlockingClause,
        ClauseSelectionT type) :
	AllSATSolver(solver), _useDecisionOnlyBlockingClause(useDecisionOnlyBlockingClause) ,
		_clauseSelection(type),_numClauseToCover(0)
{
}

SmartAllSATSolver::~SmartAllSATSolver()
{
}

const vec<Lit> & SmartAllSATSolver::generateBlockingClause(vec<Lit>& solutionCube)
{
    if (_clauseSelection == GREEDYSLOW) {

	return generateBlockingClauseGreedy(solutionCube);
    }
    throw new runtime_error("Unknown generation method");
}


/**
 * The greedy algorithm is specified as following:
 * 1. generate (regenerate) a list of clauses that each variable satisfies, update the BlockingVariables with new assignment
 * 2. find the clauses that only one literal satisfies, select these literals
 * 3. generate a list of clauses that only contains literals to be satisfied (or just count and flags)
 * 4. while(still some lits left) {
 * 		1. select a literal with highest score
 * 		2. mark all clauses that it satisfies as satisfied
 * 		3. reduce the score of all literals that would satisfy the clauses that is already satisfied.
 * 	  }
 */
//this uses a quadratic time algorithm to do this, let's get it done and try to figure out what is a better way to do it
const vec<Lit>& SmartAllSATSolver::generateBlockingClauseGreedy(vec<Lit>& solutionCube)
{
    initAssignments();
    _currentAssignment.clear();
    updateStateUponSAT();
    //we now assume that all the clauses are in the covered list
    //now we greedily select the assignments.
    findRequiredAssignments();
    initScore();
//    std::vector<int> tmpvarvec(_blockingVars.size());
//    const std::vector<CRef> & coveredClauses = getCoveredClauses();
//	std::unordered_set
//	for (int i = 0; i < coveredClauses.size(); ++ i) {
//		Clause & c = getClause(coveredClauses[i]);
//	}
//	vec <CRef> clausesToCover;
//	coveredClauses.copyTo(clausesToCover);

    int nvars = _blockingVars.size();
    _blockingVarsOrderedSet.clear();
    for (int i = 0; i < nvars; ++i) {
	if (_blockingVars[i].value == l_Undef) {
	    _blockingVarsOrderedSet.insert(&_blockingVars[i]);
//	    cerr << "inserting variable " << i << endl;
	} else {
//	    cerr << "not inserting variable" << i << endl;
	}
    }
    if (_pSolver->verbosity > 1) {
    cout << "Number of blocking vars to select from after unit prop: " << _blockingVarsOrderedSet.size() <<endl;
    cout << "vars to select:";
    for (auto itr = _blockingVarsOrderedSet.begin(); itr != _blockingVarsOrderedSet.end(); ++ itr) {
	const BlockingVariable * pbv = *itr;
	cout << " " << (pbv - &_blockingVars[0]);
    }
    cout << endl;
    }
    _stats.numTotalUndecidedVariables += _blockingVarsOrderedSet.size();
    while (_numClauseToCover > 0 && !_blockingVarsOrderedSet.empty()) {
	BlockingVariable * pbv = * (_blockingVarsOrderedSet.begin());
	int bestvid = pbv - & _blockingVars[0];
	Lit l =mkLit(bestvid, _blockingVars[bestvid].assignedValue == l_False);
	++ _stats.numTotalDecisions;
//	cerr << "Selecting literal " << signedLit(l) << " with score " << pbv->score <<endl;
	//Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
	assignLiteral(l, true);
    }
    _currentAssignment.copyTo(solutionCube);
    if (!_useDecisionOnlyBlockingClause) {
	    _currentAssignment.copyTo(_currentBlockingClause);
	    //inverse all the assignments to get a blocking clause
	    for (int i = 0; i < _currentBlockingClause.size(); ++i) {
		_currentBlockingClause[i].x ^= 1;
	    }
	    assert(checkAllClausesSatisfied());
    } else {
	//find all decisions that are useful.
        generateDecisionOnlyBlockingClause(solutionCube);
    }
    return _currentBlockingClause;

}





//will find all decision variables that support this cube
//and add them to _currentBlockingClause
//then invert them
void SmartAllSATSolver::generateDecisionOnlyBlockingClause(const vec<Lit> & cube) {
    queue<Lit> antecedent_queue;
    set<Lit> decision_set;
    for(int i = 0; i < cube.size(); ++i) {
	Lit l = cube[i];
	int vid = var(l);
	if (_blockingVars[vid].isDecision()) {
	    decision_set.insert(~l);
	} else {
	    antecedent_queue.push(l);
	}
    }
    for (auto itr = _blockingVars.begin(); itr != _blockingVars.end(); ++itr) {
	itr -> visited = false;
    }
    while(! antecedent_queue.empty()) {
	Lit l = antecedent_queue.front();
	antecedent_queue.pop();

	int vid = var(l);
	BlockingVariable & bv = _blockingVars[vid];
	if (bv.visited) continue;
	bv.visited = true;
	CRef ante_ref = bv.antecedent;
	//int dlevel= bv.dlevel;
	assert(ante_ref != CRef_Undef);
	Clause & cl = _pSolver -> clause(ante_ref);
	for (int loc = 0; loc < cl.size(); ++loc) {
	    Lit ante_lit = cl[loc];
	    int ante_vid = var(ante_lit);
	    if (ante_vid == vid) {
		assert(ante_lit == l);
	    } else {
		//assert(ante_lit evaluate to 0)
		if (_blockingVars[ante_vid].isDecision()) {
		    decision_set.insert(ante_lit);
		} else {
		    antecedent_queue.push(~ante_lit);
		}
	    }
	}
    }
    this -> _currentBlockingClause.clear();
//    this -> _currentBlockingClause.growTo(decision_set.size());
    for(auto itr = decision_set.begin(); itr != decision_set.end(); ++itr) {
	_currentBlockingClause.push(*itr);
    }
}






//check whether the _currentBlockingClause contains a blocking clause whose inverse
//would satisfy all clauses
bool SmartAllSATSolver::checkAllClausesSatisfied() {
    _tempAssignmentVec.resize(_pSolver-> nVars(), l_Undef);
    fill(_tempAssignmentVec.begin(), _tempAssignmentVec.end(), l_Undef);
    for (int i = 0; i < _currentBlockingClause.size(); ++ i) {
	Lit l = _currentBlockingClause[i];
	_tempAssignmentVec[var(l)] = sign(l) ? l_True : l_False;
    }
    const vec<CRef> & cls = this -> getCoveredClauses();
    bool allsat = true;
    for (int cid = 0; cid < cls.size(); ++ cid) {
	const Clause & cl = _pSolver -> clause(cls[cid]);
	bool sat = false;
	for (int i = 0; i < cl.size(); ++i) {
	    Lit l = cl[i];
	    lbool val = _tempAssignmentVec[var(l)];
	    if ((val == l_True && (!sign(l))) || (val == l_False && sign(l))) {
		sat = true;
		break;
	    }
	}
	if (!sat) {
	    cerr << "clause not satisfied:";
	    for (int i = 0; i < cl.size(); ++ i) {
		Lit lit = cl[i];
		lbool v = _tempAssignmentVec[var(lit)];
		char ch = v == l_True ? 'T' : (v == l_False ? 'F' : '*');
		cerr << (sign(lit) ? '-':'+') << (var(lit)) << '(' << ch << ") ";
	    }
	    cerr << endl;
	    allsat = false;
	}
    }
    return allsat;
}

//initialize score to be the number of clauses a variable can satisfy when it's assigned to the current assignment
void SmartAllSATSolver::initScore()
{
    for (auto itr = _blockingVars.begin(); itr != _blockingVars.end(); ++itr) {
	(*itr).score = 0;
    }
    const vec<CRef> & allclauses = this->getCoveredClauses();
    for (int i = 0; i < allclauses.size(); ++i) {
	if (_clauseSatisfied[allclauses[i]] == 1)
	    continue;
	Clause & cl = _pSolver->clause(allclauses[i]);
	for (int loc = 0; loc < cl.size(); ++ loc) {
	    if (_pSolver-> modelValue(cl[loc]) == l_True)
		++_blockingVars[var(cl[loc])].score;
	}
    }
}

static void printLiteral(Lit lit, ostream & os) {
    os << (sign(lit) == 1 ? '-' : '+') << var(lit);
}

ostream & SmartAllSATSolver::printClause(const Clause & cl, ostream & os) 
{
    int sz = cl.size();
    for (int i = 0; i < sz; ++i) {
	printLiteral(cl[i], os);
	os << " ";
    }
    return os;
}

//this routine updates the literal and potentially also update the score upon assignment
void SmartAllSATSolver::assignLiteral(Lit l, bool updateScore) {
    BlockingVariable & bv = _blockingVars[var(l)];
    if (bv.value == bv.assignedValue) {
	return;
    }
    assert (bv.value == l_Undef);
    bv.value = bv.assignedValue;
    if (updateScore) {
	BlockingVariableOrderedSet::iterator pitr = _blockingVarsOrderedSet.find(&bv);
	assert(pitr != _blockingVarsOrderedSet.end());
	_blockingVarsOrderedSet.erase(pitr);
    }
    assert(bv.assignedValue == lbool(!sign(l))); //note that 0=l_True, 1=l_False
    const vector<CRef> & list = bv.coveredClauses[sign(l)];
    if (_pSolver->verbosity>1) {
	cout << "Assignment literal ";
        printLiteral(l, cout);
	cout << " covers " << list.size() << " clauses :";
	for (auto itr = list.begin(); itr < list.end(); ++itr) {
	    cout << " " << (*itr);
	}
	cout <<endl;
    }
    for (auto itr = list.begin(); itr != list.end(); ++itr) {
	if (_clauseSatisfied[*itr] != 1) {
	    -- _numClauseToCover;
	    if (_pSolver->verbosity > 1) {
		Clause & cl = _pSolver -> clause(*itr);
		cout << "clause (" << (*itr) << ")";
		printClause(cl, cout);
		cout <<"satisfied, now " << _numClauseToCover << " clauses to cover" <<endl;

	    }
	    if (updateScore) {
		Clause & cl = _pSolver -> clause(*itr);
		for (int loc = 0; loc < cl.size(); ++ loc) {
		    int nvid = var(cl[loc]);
		    if (_pSolver -> modelValue(cl[loc]) == l_True && _blockingVars[nvid].value == l_Undef) {
			BlockingVariableOrderedSet::iterator pitr2 = _blockingVarsOrderedSet.find(&(_blockingVars[nvid]));
			assert(pitr2 != _blockingVarsOrderedSet.end());
			_blockingVarsOrderedSet.erase(pitr2);
			-- _blockingVars[nvid].score;
			if (_blockingVars[nvid].score > 0)
			    _blockingVarsOrderedSet.insert(&(_blockingVars[nvid]));
		    }
		}
	    }
	    _clauseSatisfied[*itr] = 1;
	} else {
	    if (_pSolver->verbosity > 2) {
	        cout << "clause ("<<(*itr)<<") ";
	        printClause(_pSolver -> clause(*itr),cout);
	        cout << " is already marked satisfied"<<endl;
	    }
	}

    }
    _currentAssignment.push(l);

}


void SmartAllSATSolver::initAssignments()
{
    if (_blockingVars.empty()) {
	_blockingVars.resize(_pSolver-> nVars());
    }
    assert(_blockingVars.size() == _pSolver -> nVars());
    for (int vid = 0; vid < _blockingVars.size(); ++ vid) {
	_blockingVars[vid].score = 0;
	_blockingVars[vid].assignedValue = _pSolver -> model[vid];
	_blockingVars[vid].value = l_Undef;
	_blockingVars[vid].antecedent = _pSolver -> antecedentClause(vid);
	_blockingVars[vid].dlevel = _pSolver -> decisionLevel(vid);

    }
}
//check if a clause is only satisfied by a single literal, if so that literal should be included

static const char* boolName(lbool val) {
    if (val == l_True) 
	return "True"; 
    else if (val == l_False) 
	return "False"; 
    else 
	return "Unknown";
}

void SmartAllSATSolver::findRequiredAssignments()
{
    _currentAssignment.clear(false);

    const vec<CRef> & allclauses = this->getCoveredClauses();
    _numClauseToCover = allclauses.size();
     if (_pSolver->verbosity > 0) cout << "Need to cover " << _numClauseToCover << " clauses" <<endl;
//    for (int i = 0; i < _numClauseToCover; ++ i ) {
//	cerr << ""
//    }
//    _clauseSatisfied.resize(_numClauseToCover);
    _clauseSatisfied.clear();
    for (int i = 0; i < allclauses.size(); ++i) {
	_clauseSatisfied[allclauses[i]] = 0;
    }
    if (_pSolver->verbosity == 1) cout << "Literals unit by clause:";
    for (auto itr = _pSolver -> _singleLits.begin(); itr != _pSolver -> _singleLits.end();
	    ++itr) {
	if (_pSolver->verbosity > 1) {
	    cout << "Literal ";
	    printLiteral(*itr, cout);
	    cout << " is required from single literal input clause" << endl;
	} else if (_pSolver->verbosity == 1) {
	    printLiteral(*itr, cout);
	    cout << " ";
	}
	assignLiteral(*itr, false);
    }
    for (int i = 0; i < allclauses.size(); ++i) {
	if (_clauseSatisfied[allclauses[i]] == 1)
	    continue;
	const Clause & cl = _pSolver->clause(allclauses[i]);
	int num1 = 0;
	int litloc = -1;
	for (int loc = 0; loc < cl.size(); ++loc) {
	    Lit l = cl[loc];
	    if (_pSolver->verbosity > 2) 
		cout << "Literal " << (sign(l) == 1 ? '-' : '+') << var(l) << " var value is " << boolName(_pSolver->modelValue(var(l)))  << endl;

	    if (_pSolver->modelValue(l) == l_True) {
		++num1;
		litloc = loc;
	    }
	}
	if (num1 == 0) {
	    cerr << "clause not satisfied:";
	    for (int loc = 0; loc < cl.size(); ++ loc) {
		Lit l = cl[loc];
		cerr << " " << (sign(l) ? '-' : '+') << var(l);
	    }
	    cerr << endl;
	}
	assert(num1 > 0);
	if (num1 == 1) {
	    if (_pSolver -> verbosity == 1) {
	        Lit l = cl[litloc];
	        int svid = sign(l)  ? var(l) : - var(l);
	        cout << " " << svid;
	    } else if (_pSolver -> verbosity > 1) {
		cout << "Assignment forcing clause:";
		for (int loc = 0; loc < cl.size(); ++ loc) {
		    Lit lit = cl[loc];
		    cout << " " <<(sign(lit) == 1 ? '-' : '+') << var(lit);
		}
		cout << endl;
		cout << "Location in clause: " << litloc << " ";
	        Lit l = cl[litloc];
		cout << "Forced Assignment:" << (sign(l) == 1 ? '-' : '+') << var(l) << endl;
	    }
	    assignLiteral(cl[litloc], false);
	}
    }
    if (_pSolver -> verbosity > 1)  cout << endl;
    if (_pSolver -> verbosity > 0) 
	 cout << "Number of clauses to cover after unit assignments:" << _numClauseToCover <<endl;
}



} /* namespace Allsat */
