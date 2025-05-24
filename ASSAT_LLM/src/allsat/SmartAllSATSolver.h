/*
 * SmartAllSATSolver.h
 *
 *  Created on: Mar 8, 2013
 *      Author: yinlei
 */

#ifndef SMARTALLSATSOLVER_H_
#define SMARTALLSATSOLVER_H_

#include "AllSATSolver.h"
#include <vector>
#include <set>
#include <iostream>
#include <unordered_map>

namespace Allsat {

    enum ClauseSelectionT {
	GREEDYSLOW, INVALIDALGO
    };


    class BlockingVariable {
    public:
	Minisat::lbool assignedValue;
	Minisat::lbool value;
	Minisat::CRef antecedent;
	int dlevel;
	std::vector<Minisat::CRef> coveredClauses[2];
	int score;
	mutable bool visited;
	bool isDecision() {return antecedent == Minisat::CRef_Undef;}
    };

    struct gt_BlockingVariable {
	bool operator()(const BlockingVariable * b1,
	        const BlockingVariable* b2) const
	{
	    return (b1->score > b2->score) || (b1->score == b2-> score && b1 < b2);
	}
    };
    typedef std::set<BlockingVariable*, gt_BlockingVariable> BlockingVariableOrderedSet;

    class SmartAllSATSolver: public AllSATSolver {
    public:
	SmartAllSATSolver(AccessSolver * solver, bool useDecisionOnlyBlockingClause, ClauseSelectionT type = GREEDYSLOW);
	virtual ~SmartAllSATSolver();
	virtual const Minisat::vec<Minisat::CRef> & getCoveredClauses() = 0;
	virtual void updateStateUponSAT() = 0;  //generate (regenerate) a list of clauses that each variable satisfies
	virtual const Minisat::vec<Minisat::Lit> & generateBlockingClause(Minisat::vec<Minisat::Lit>& solutionCube);

    protected:
	void copyModel();
	ClauseSelectionT _clauseSelection;
	Minisat::vec<Minisat::CRef> _coveredClauses;
	const Minisat::vec<Minisat::Lit> &generateBlockingClauseGreedy(Minisat::vec<Minisat::Lit>& solutionCube);
	void initScore();
	void findRequiredAssignments(); //the required assignments are put into this vec
//	bool clauseSatisfied(Minisat::CRef cref);
	void generateDecisionOnlyBlockingClause(const Minisat::vec<Minisat::Lit> & cube);

	std::vector<BlockingVariable> _blockingVars;

	bool _useDecisionOnlyBlockingClause;


	void initAssignments(); // clear _currentAssignment, allocate _blockingVars if necessary, clear score and assignment, put in cur
	void assignLiteral(Minisat::Lit l, bool updateScore); //assign the literal l, put it at the end of _currentAssignment, propagate _clauseSatisfied and change _numClauseToCover
	Minisat::vec<Minisat::Lit> _currentAssignment;
	Minisat::vec<Minisat::Lit> _currentBlockingClause;
	std::unordered_map<Minisat::CRef, int> _clauseSatisfied;
	int _numClauseToCover;
	BlockingVariableOrderedSet _blockingVarsOrderedSet;
	bool checkAllClausesSatisfied();
	static std::ostream & printClause(const Minisat::Clause & cl, std::ostream & os = std::cout);
    private:
	std::vector<Minisat::lbool> _tempAssignmentVec;

    };

} /* namespace Allsat */
#endif /* SMARTALLSATSOLVER_H_ */
