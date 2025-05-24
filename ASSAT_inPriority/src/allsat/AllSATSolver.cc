/*
 * AllSATSolver.cc
 *
 *  Created on: Mar 3, 2013
 *      Author: yinlei
 */

#include "AllSATSolver.h"
#include "utils/System.h"
#include <iostream>
using namespace Minisat;
using namespace std;
namespace Allsat {
AllSATSolver::AllSATSolver(AccessSolver * psolver) :
	_pSolver(psolver), _status(Allsat::UNKNOWN)
{
    _stats.numVariables = psolver -> nVars();
    _stats.numClauses = psolver -> nClauses();
    _stats.numTotalDecisions = 0;
    _stats.numTotalUndecidedVariables = 0;
    _stats.numTotalUncoveredClauses = 0;
    _stats.numBlockingClauses = 0;
    _stats.numBlockingLits = 0;
    _stats.numSolutionLits = 0;

    _stats.numSATs = 0;
    _stats.firstSATCPUTime = -1.0;

    _limits.maxBlockingClauses = INT32_MAX;

}

AllSATSolver::~AllSATSolver()
{
}

void AllSATSolver::addBlockingClause(const vec<Lit>& lits)
{
    _blockingClauses.resize(_blockingClauses.size() + 1);
    vector<Lit> & v = _blockingClauses.back();
    v.resize(lits.size());
    for (int i = 0; i < lits.size(); ++i) {
	v[i] = lits[i];
    }
    _pSolver->addClause(lits);

}

void AllSATSolver::dumpAllSATBlockingClauses(std::ostream & os)
{
    long litcount = 0l;
    for (vector<vector<Lit> >::const_iterator itr = _blockingClauses.begin();
	    itr != _blockingClauses.end(); ++itr) {
	litcount += (*itr).size();
    }
    //cerr << "There are total " << _blockingClauses.size()
	//    << " blocking clauses, with total " << litcount << "literals:"
	//    << endl;
    for (vector<vector<Lit> >::const_iterator itr = _blockingClauses.begin();
	    itr != _blockingClauses.end(); ++itr) {
	for (vector<Lit>::const_iterator litr = (*itr).begin();
	        litr != (*itr).end(); ++litr) {
	    char pol = sign(*litr) == 0 ? '+' : '-';
	    os << pol << (var(*litr) + 1) << ' ';
	}
	os << '0' << endl;
    }
}
void AllSATSolver::dumpAllSATSolutionCubes(std::ostream & os)
{
    long litcount = 0l;
    for (vector<vector<Lit> >::const_iterator itr = _solutionCubes.begin();
	    itr != _solutionCubes.end(); ++itr) {
	litcount += (*itr).size();
    }
    //cerr << "There are total " << _solutionCubes.size()
	//    << " solution cubes, with total " << litcount << "literals:"
	//    << endl;
    for (vector<vector<Lit> >::const_iterator itr = _solutionCubes.begin();
	    itr != _solutionCubes.end(); ++itr) {
	for (vector<Lit>::const_iterator litr = (*itr).begin();
	        litr != (*itr).end(); ++litr) {
	    char pol = sign(*litr) == 0 ? '+' : '-';
	    os << pol << (var(*litr) + 1) << ' ';
	}
	os << '0' << endl;
    }
}
bool AllSATSolver::solve()
{
    lbool res;
    _startCPUTime = cpuTime();
    while ((res = _pSolver->solveCustom()) == l_True) {
	if (_stats.firstSATCPUTime < 0.0) {
	    _stats.firstSATCPUTime = cpuTime() - _startCPUTime;
	}
	++_stats.numSATs;
	if (_pSolver->verbosity > 0) cerr << "SAT #" << _stats.numSATs << endl;
	//const vec<CRef> & newcl = getCoveredClauses();
	const vec<lbool> & model = getModel();

	std::vector<int> *to_save = new std::vector<int>();
	for (int i = 0; i < model.size(); ++i){
		if (model[i] == l_True){
			to_save->push_back(i+1);
		}
		else{
			to_save->push_back(-1*(i+1));
		}
	}
	models->push_back(to_save);

	/*for (vector<int>::iterator v = to_save->begin(); v != to_save->end(); v++){
		cout << *v << " ";
	}
	cout << endl;
	cout << models->size() << endl;*/

	if (_pSolver->verbosity>1) {
	    std::cout << "Model: ";
	    for (int i = 0; i < model.size(); ++ i) {
	        char ch = (model[i] == l_True) ? '+' :( (model[i] == l_False) ? '-' : '*');
	        std::cout <<' '<< ch << i;
	    }
	    std::cout << std::endl;
	}
	vec<Lit> solutionCube;
	const vec<Lit> & new_clause = generateBlockingClause(solutionCube);
	if ( true || _pSolver -> verbosity > 1) {
	    //cout << "New blocking clause with " << new_clause.size() << " literals:";
//	    for (int i=0; i < new_clause.size(); ++ i) {
//	        cout << " " << signedLit(new_clause[i]);
//	    }
//	    cout << endl;
	}
    // std::cout << "blocking clause: " << new_clause << std::endl;

	_pSolver->backtrack(0);
	++_stats.numBlockingClauses;
	_stats.numBlockingLits += new_clause.size();
	_stats.numSolutionLits += solutionCube.size();
	_blockingClauses.resize(_blockingClauses.size() +1);
	_solutionCubes.resize(_solutionCubes.size() + 1);
	vector<Lit> & v = _blockingClauses.back();
	v.resize(new_clause.size());

	vector<int> *new_block = new vector<int>();
	for (int i = 0; i < new_clause.size(); ++ i) {
	    v[i] = new_clause[i];
	    new_block->push_back(signedLit(new_clause[i]));
	}
	blocking->push_back(new_block);

	vector<Lit> & v2 = _solutionCubes.back();
	v2.resize(solutionCube.size());
	for (int i = 0; i < solutionCube.size(); ++i) {
	    v2[i] = solutionCube[i];
	}
	bool result = _pSolver->addClause(new_clause);
	if (!checkLimits()) {
	    std::cerr << "LIMIT Exceeded for reason " << reason(_status)
		    << ", exiting...";
	    return false;
	}
    }
    if (res == l_Undef) {
	return false;
    }
    if (_stats.numSATs == 0) {
	//cout << "UNSATISFIABLE" << endl; //FC
	return true;
    }
//    cout << "Total " << _stats.numBlockingClauses << " Blocking clauses, total " << _stats.numBlockingLits << " lits." <<endl;
//    cout << "Blocking clauses:" <<endl;
//    for (auto citr = _blockingClauses.begin(); citr != _blockingClauses.end(); ++ citr) {
//	for (auto litr = citr-> begin(); litr != citr-> end(); ++ litr) {
//	    cout << (sign(*litr) ? '-' :'+') << (var(*litr) + 1) << " ";
//	}
//	cout << "0" <<endl;
//    }
    return true;
}
//check if time, lits, clause limits are voilated.
bool AllSATSolver::checkLimits()
{
    if (_stats.numBlockingClauses > _limits.maxBlockingClauses) return false;
    return true;
}



const std::string & AllSATSolver::reason(Allsat::AllSATStatusT status)
{
    static const std::string reasons[] = { "Unknown", "AllSolutionsFound",
	    "Timeout", "MemoryOut", "Too Many Blocking Clauses",
	    "Too many Blocking Literals", "Invalid reason" };
    int i = status;
    if (i < 0 || i > 6)
	i = 6;
    return reasons[i];
}
bool AllSATSolver::solveReachability(AllSATSolver* toCNFSolver)
{
    lbool res;
    _startCPUTime = cpuTime();
    while ((res = _pSolver->solveCustom()) == l_True) {
        if (_stats.firstSATCPUTime < 0.0) {
            _stats.firstSATCPUTime = cpuTime() - _startCPUTime;
        }
        ++_stats.numSATs;
#if 0
        cerr << "SAT #" << _stats.numSATs << endl;
#endif
        //const vec<CRef> & newcl = getCoveredClauses();
#if 0
        const vec<lbool> & model = getModel();
        std::cout << "Model: ";
        for (int i = 0; i < model.size(); ++ i) {
            char ch = (model[i] == l_True) ? '+' :( (model[i] == l_False) ? '-' : '*');
            std::cout <<' '<< ch << i;
        }
        std::cout << std::endl;
#endif
        vec<Lit> solutionCube;
        const vec<Lit> & blocking_clause = generateBlockingClause(solutionCube);
        vec<Lit> new_clause(blocking_clause.size());
        for(int i=0; i!=blocking_clause.size(); i++) new_clause[i] = blocking_clause[i];

#if 0
        std::cout << "initial clause : " << new_clause << std::endl;
        std::cout << "initial cube   : " << solutionCube << std::endl;
#endif
        pruneVec(new_clause);
        pruneVec(solutionCube);
#if 0
        std::cout << "pruned clause  : " << new_clause << std::endl;
        std::cout << "pruned cube    : " << solutionCube << std::endl;
#endif

#if 0
        //cerr << "New blocking clause with " << new_clause.size() << " literals:";
        for (int i=0; i < new_clause.size(); ++ i) {
            cerr << " " << signedLit(new_clause[i]);
        }
        cerr << endl;
#endif
        _pSolver->backtrack(0);
        ++_stats.numBlockingClauses;

        _stats.numBlockingLits += new_clause.size();
        _stats.numSolutionLits += solutionCube.size();

        _blockingClauses.resize(_blockingClauses.size() +1);
        _solutionCubes.resize(_solutionCubes.size() + 1);

        _pSolver->addClause(new_clause);
        bool result = toCNFSolver->_pSolver->addOrigClause(new_clause);

        if (!checkLimits()) {
            std::cerr << "LIMIT Exceeded for reason " << reason(_status)
                << ", exiting...";
            return false;
        }
    }
    if (res == l_Undef) {
        return false;
    }
    if (_stats.numSATs == 0) {
        return true;
    }

    vec<Lit> assump;
    return toCNFSolver->solve();
}

void AllSATSolver::pruneVec(vec<Lit>& v)
{
    int pos=0;
    for(int i=0; i != v.size(); i++) {
#if 0
        std::cout << "var(v[i])=" << var(v[i]) << std::endl;
        std::cout << "isNextStateVar=" << _pSolver->isNextStateVar(var(v[i])) << std::endl;
#endif
        if(_pSolver->isNextStateVar(var(v[i]))) {
            v[pos] = v[i];
            pos++;
        }
#if 0
        std::cout << "pos=" << pos << std::endl;
#endif
    }
    v.shrink(v.size() - pos);
}

std::ostream& operator<<(std::ostream& out, const Minisat::vec<Minisat::Lit>& v)
{
    for(int i = 0; i != v.size(); i++) {
        out << v[i] << " ";
    }
    return out;
}

std::ostream& operator<<(std::ostream& out, const Minisat::Lit& l) {
    int vid = Minisat::var(l);
    if(sign(l)) out << "-" << vid;
    else out << "+" << vid;
    return out;
}

void AllSATSolver::addVars(AccessSolver* solver)
{
    while(_pSolver->nVars() < solver->nVars()) {
        _pSolver->newVar();
    }
}


}

