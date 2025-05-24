/**
 * @file 		CompleteSemantics.cpp
 * @class 		CompleteSemantics
 * @brief 		Class for the complete semantics
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "CompleteSemantics.h"
#include <stlsoft/util/exception_string.hpp>

/**
 * @brief Computing semantics extensions
 */
bool CompleteSemantics::compute(Argument *arg, bool firstonly)
{
	if (this->conf->allSat())
	{
		if (arg != NULL)
		{
			throw new AllSATException();
		}
		return this->allsat(this->sat_pigreek, &(this->labellings), NULL, NULL,
				-1);
	}
	else
	{

		this->cleanlabs();
		SATFormulae cnf = SATFormulae(3 * this->af->numArgs());
		this->sat_pigreek.clone(&cnf);

		SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

		do
		{
			Labelling res = Labelling();

			SATFormulae cnf_AND_cnfdf = SATFormulae(3 * this->af->numArgs());
			cnf.clone(&cnf_AND_cnfdf);
			cnfdf.merge(&cnf_AND_cnfdf);

			if (!this->satlab(cnf_AND_cnfdf, &res))
			{
				break;
			}

			if (arg != NULL)
			{
				if (res.inargs()->exists(arg) == false)
					return false;
			}
			else
			{
				this->labellings.push_back(res);
			}

			if (firstonly)
				return true;

			OrClause oppsolution = OrClause();

			for (SetArgumentsIterator arg = res.inargs()->begin();
					arg != res.inargs()->end(); arg++)
			{
				oppsolution.appendVariable((*arg)->NotInVar());
			}

			for (SetArgumentsIterator arg = res.outargs()->begin();
					arg != res.outargs()->end(); arg++)
			{
				oppsolution.appendVariable((*arg)->NotOutVar());
			}

			for (SetArgumentsIterator arg = res.undecargs()->begin();
					arg != res.undecargs()->end(); arg++)
			{
				oppsolution.appendVariable((*arg)->NotUndecVar());
			}

			cnfdf.appendOrClause(oppsolution);

		} while (true);
		return true;
	}

}

bool CompleteSemantics::credulousAcceptance(Argument *arg)
{
	return super::credulousAcceptance(arg);
}

bool CompleteSemantics::skepticalAcceptance(Argument *arg)
{
	this->cleanlabs();
	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf);

	while (true)
	{
		Labelling res = Labelling();
		if (!this->satlab(cnf, &res))
		{
			break;
		}

		if (!res.inargs()->exists(arg))
			return false;

		if (res.undecargs()->cardinality() == af->numArgs())
			break;

		SetArgumentsIterator iter;
		//OrClause remove_complete_from_cnf = OrClause();
		for (iter = res.undecargs()->begin(); iter != res.undecargs()->end();
				iter++)
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
		for (iter = res.inargs()->begin(); iter != res.inargs()->end(); iter++)
		{
			remaining.appendVariable((*iter)->UndecVar());
		}
		cnf.appendOrClause(remaining);
	}
	return true;
}

SetArguments *CompleteSemantics::someExtension()
{
	this->compute(NULL, true);
	if (this->labellings.empty())
		return NULL;
	return this->labellings.at(0).inargs();
}

CompleteSemantics::~CompleteSemantics()
{
// TODO Auto-generated destructor stub
}

