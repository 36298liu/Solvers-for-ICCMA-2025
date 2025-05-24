/**
 * @file 		StableSemantics.cpp
 * @class 		StableSemantics
 * @brief 		Class for the stable semantics
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "StableSemantics.h"

/**
 * @brief Computing semantics extensions
 */
bool StableSemantics::compute(Argument *arg, bool firstonly)
{

	if (this->conf->allSat() && arg == NULL)
	{
		bool res = this->allsat(this->sat_pigreek, &(this->labellings), NULL,
		NULL, -1);

		// SE
		if (firstonly)
		{
			int topop = this->labellings.size() - 1;
			for (int i = 0; i < topop; i++)
			{
				this->labellings.pop_back();
			}
		}

		return res;
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

			if (this->conf->isIn())
			{
				for (SetArgumentsIterator arg = res.outargs()->begin();
						arg != res.outargs()->end(); arg++)
				{
					oppsolution.appendVariable((*arg)->InVar());
				}
				cnfdf.appendOrClause(oppsolution);
			}

			if (this->conf->isOut())
			{
				oppsolution = OrClause();

				for (SetArgumentsIterator arg = res.inargs()->begin();
						arg != res.inargs()->end(); arg++)
				{
					oppsolution.appendVariable((*arg)->OutVar());
				}
				cnfdf.appendOrClause(oppsolution);
			}
		} while (true);
	}
	return true;

	//return super::compute(arg, firstonly);
	//if (this->labellings.size() == 1 && this->labellings.at(0).inargs()->empty() && this->af->numArgs() != 0)
	//	this->labellings.clear();
}

bool StableSemantics::credulousAcceptanceComplete(Argument *arg)
{
	return super::credulousAcceptance(arg);
}
bool StableSemantics::credulousAcceptanceImproved(Argument *arg)
{
	Labelling res = Labelling();
	if(this->satlab(sat_pigreek, &res))
	{
		SATFormulae compute = SATFormulae(3 * this->af->numArgs());
		this->sat_pigreek.clone(&compute);
		compute.appendOrClause(OrClause(1, arg->InVar()));
		Labelling res = Labelling();
		if(this->satlab(compute, &res))
			return true;
		else
			return false;
	}
	return false;
}

bool StableSemantics::skepticalAcceptanceImproved(Argument *arg)
{
	Labelling res = Labelling();
	if(this->satlab(sat_pigreek, &res))
	{
		SATFormulae compute = SATFormulae(3 * this->af->numArgs());
		this->sat_pigreek.clone(&compute);
		compute.appendOrClause(OrClause(1, arg->OutVar()));
		Labelling res = Labelling();
		if(this->satlab(compute, &res))
			return false;
		else
			return true;
	}
	return true;
}

bool StableSemantics::credulousAcceptance(Argument *arg)
{
	if (this->conf->isDCImpr())
	{
		return this->credulousAcceptanceImproved(arg);
	}
	else
	{
		return this->credulousAcceptanceComplete(arg);
	}
}

bool StableSemantics::skepticalAcceptance(Argument *arg)
{
	if (this->conf->isDSImpr())
	{
		return this->skepticalAcceptanceImproved(arg);
	}
	else
	{
		return this->compute(arg, false);
	}
}

/*bool StableSemantics::skepticalAcceptance(Argument *arg)
{
	this->cleanlabs();
	SATFormulae compute = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&compute);

	compute.appendOrClause(OrClause(1, arg->OutVar()));

	Labelling res = Labelling();
	if (this->satlab(compute, &res, false))
		return false;

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

}*/

SetArguments *StableSemantics::someExtension()
{
	this->compute(NULL, true);
	if (this->labellings.empty()
			|| (this->labellings.empty() && this->af->numArgs() != 0))
		return NULL;
	else
		return this->labellings.at(0).inargs();
}

StableSemantics::~StableSemantics()
{
	// TODO Auto-generated destructor stub
}

