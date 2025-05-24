/*
 * AccessSolver.cc
 *
 *  Created on: Mar 9, 2013
 *      Author: yinlei
 */

#include "AccessSolver.h"

namespace Allsat {
bool AccessSolver::addOrigClause(Minisat::vec<Minisat::Lit> & ps) {
    if (ps.size() == 1) {
	_singleLits.push_back(ps[0]);
    }
    bool slRet;
    Minisat::Lit slOut;
    bool stillSAT = Minisat::Solver::addOrigClause(ps, slRet, slOut);
    if(slRet) {
        _singleLits.push_back(slOut);
    }
}

} /* namespace Allsat */
