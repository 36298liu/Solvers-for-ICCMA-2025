/**
 * @file 		GroundedSemantics.cpp
 * @class 		GroundedSemantics
 * @brief 		Class for the grounded semantics
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "GroundedSemantics.h"

/**
 * @brief Computing semantics extensions
 */
bool GroundedSemantics::compute(Argument *arg, bool firstonly)
{
	this->cleanlabs();
	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf);

	Labelling grcand = Labelling();


	while (true)
	{
		Labelling res = Labelling();
		if (!this->satlab(cnf, &res))
		{
			break;
		}

		grcand = Labelling();

		res.clone(&grcand);
		if (res.undecargs()->cardinality() == af->numArgs())
			break;

		SetArgumentsIterator iter;
		//OrClause remove_complete_from_cnf = OrClause();
		for (iter = res.undecargs()->begin(); iter != res.undecargs()->end(); iter++)
		{
			cnf.appendOrClause(OrClause(1, (*iter)->UndecVar()));
			//remove_complete_from_cnf.appendVariable((*iter)->NotInVar());
		}
		//cnf.appendOrClause(remove_complete_from_cnf);

		OrClause remaining = OrClause();
		for (iter = res.outargs()->begin(); iter != res.outargs()->end();
				iter++)
		{
			remaining.appendVariable((*iter)->UndecVar());
		}
		for (iter = res.inargs()->begin(); iter != res.inargs()->end();
				iter++)
		{
			remaining.appendVariable((*iter)->UndecVar());
		}
		cnf.appendOrClause(remaining);
	}

	if (arg == NULL)
	{
		this->labellings.push_back(grcand);
	}
	else
	{
		return grcand.inargs()->exists(arg);
	}
	return true;
}

bool GroundedSemantics::credulousAcceptance(Argument *arg)
{
	return this->compute(arg);
}

bool GroundedSemantics::skepticalAcceptance(Argument *arg)
{
	return this->compute(arg);
}

SetArguments *GroundedSemantics::someExtension()
{
	this->compute();
	return this->labellings.at(0).inargs();
}

GroundedSemantics::~GroundedSemantics()
{
// TODO Auto-generated destructor stub
}

