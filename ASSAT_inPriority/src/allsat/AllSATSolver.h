/*
 * AllSATSolver.h
 *
 *  Created on: Mar 3, 2013
 *      Author: yinlei
 */

#ifndef ALLSATSOLVER_H_
#define ALLSATSOLVER_H_

#include "mtl/Vec.h"
#include "AccessSolver.h"
#include <vector>
#include <string>
#include <iostream>

extern std::vector<std::vector <int> *> *models;
extern std::vector<std::vector <int> *> *blocking;

namespace Allsat {

    enum AllSATStatusT {
	UNKNOWN,
	ALLSAT_SUCCESSFUL,
	ALLSAT_TIMEOUT,
	ALLSAT_MEMOUT,
	ALLSAT_TOOMANYBLOCKINGCLAUSES,
	ALLSAT_TOOMANYBLOCKINGLITS,
	INVALID,
    };

    struct AllSATStats {
	int numVariables;
	int numClauses;
	int numBlockingClauses;
	int numTotalDecisions;
	int numTotalUndecidedVariables;
	int numTotalUncoveredClauses;
	int64_t numBlockingLits;
	int64_t numSolutionLits;
	int64_t runtimeMillis;
	int numSATs;
        double firstSATCPUTime;
    };

    struct AllSATLimits {
	int maxBlockingClauses;
	int64_t maxBlockingLits;
	int maxRuntimeMillis;
	int maxNumSATs;
    };



    class AllSATSolver {
    public:
	AllSATSolver(AccessSolver * solver);
	virtual ~AllSATSolver();

	const Minisat::vec<Minisat::lbool> & getModel();
	virtual const Minisat::vec<Minisat::CRef> & getCoveredClauses() = 0;

	void addBlockingClause(const Minisat::vec<Minisat::Lit>& lits);

	void addSolutionCube(const Minisat::vec<Minisat::Lit> & lits);

	virtual const Minisat::vec<Minisat::Lit>& generateBlockingClause(Minisat::vec<Minisat::Lit> & solutionCubeLits) = 0;

	void dumpAllSATBlockingClauses(std::ostream & os = std::cout);

	void dumpAllSATSolutionCubes(std::ostream & os = std::cout);

	bool solve();
	bool solveReachability(AllSATSolver* toCNFSolver);
    void pruneVec(Minisat::vec<Minisat::Lit>& v);

	static const std::string & reason(AllSATStatusT status);
	static int signedLit(Minisat::Lit l) {
	    int vid = Minisat::var(l);
	    return sign(l) ? -1 * (vid + 1): vid + 1;
	}
	AllSATStats _stats;

	void setMaxBlockingClause(int bcMax) {_limits.maxBlockingClauses = bcMax;}

    void addVars(AccessSolver* solver);


    protected:
	AccessSolver* _pSolver;

	std::vector<std::vector<Minisat::Lit> > _blockingClauses;
	std::vector<std::vector<Minisat::Lit> > _solutionCubes;

	AllSATLimits _limits;
	AllSATStatusT _status;
	double _startCPUTime;

    private:
	bool checkLimits(); //it would change _status to appropriate status return true if limits are not breached

    };


    inline const Minisat::vec<Minisat::lbool> & AllSATSolver::getModel()
    {
	return _pSolver->model;
    }

    std::ostream& operator<<(std::ostream& out, const Minisat::vec<Minisat::Lit>& v);
    std::ostream& operator<<(std::ostream& out, const Minisat::Lit& l);
}/*Namespace Allsat*/

#endif /* ALLSATSOLVER_H_ */
