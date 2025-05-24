/**
 * @file 		PreferredSemantics.cpp
 * @class 		PreferredSemantics
 * @brief 		Class for the preferred semantics for an AF
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "PreferredSemantics.h"

/**
 * @see CompleteSemantics#CompleteSemantics
 */
PreferredSemantics::PreferredSemantics(AF *the_af, Encoding enc,
		ConfigurationPreferred *c, ConfigurationStable *cStab) :
		super(the_af, enc)
{
	this->conf = c;
	this->confStable = cStab;
}

/**
 * @brief                       This is the function that in TAFA-13 is described by Algorithm 1
 * @details                     This function has been rewritten for adhering to Algorithm 1 of TAFA-13, but the one used for
 *                                      the empirical evaluation in TAFA-13 was slightly different as it adopts some straightforward optimisations
 */
bool PreferredSemantics::compute(Argument *arg, bool firstonly)
{
	this->cleanlabs();
	SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

	if (this->conf->isStableUsed())
	{
		SATFormulae cnfs = SATFormulae(3 * this->af->numArgs());
		this->sat_pigreek.clone(&cnfs);

		for (SetArgumentsIterator arg = this->af->begin();
				arg != this->af->end(); arg++)
			cnfs.appendOrClause(OrClause(1, (*arg)->NotUndecVar()));

		if (this->confStable->allSat())
		{

			//throw new ConfigurationPreferredExperimental();

			vector<OrClause> blocking;
			this->allsat(cnfs, &(this->labellings), &blocking, this->confStable, this->af->numArgs());


			// DS
			if (arg != NULL)
			{
				for (vector<Labelling>::iterator l = this->labellings.begin();
						l != this->labellings.end(); l++)
				{
					if (!(*l).inargs()->exists(arg))
						return false;
				}
				return true;
			}

			// SE
			if (firstonly)
			{
				int topop = this->labellings.size() - 1;
				for (int i = 0; i < topop; i++)
				{
					this->labellings.pop_back();
				}
			}

			for (vector<OrClause>::iterator b = blocking.begin();
					b != blocking.end(); b++)
			{
					cnfdf.appendOrClause((*b));
			}

			if (debug)
			{
				cout << "Blocking" << endl;
				cout << cnfdf.toString() << endl;
			}
		}
		else
		{
			do
			{
				Labelling res = Labelling();

				SATFormulae cnfs_AND_cnfdf = SATFormulae(
						3 * this->af->numArgs());
				cnfs.clone(&cnfs_AND_cnfdf);
				cnfdf.merge(&cnfs_AND_cnfdf);

				if (!this->satlab(cnfs_AND_cnfdf, &res))
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

				if (this->confStable->isIn())
				{
					for (SetArgumentsIterator arg = res.outargs()->begin();
							arg != res.outargs()->end(); arg++)
					{
						oppsolution.appendVariable((*arg)->InVar());
					}
					cnfdf.appendOrClause(oppsolution);
				}

				if (this->confStable->isOut())
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
	}

	this->add_non_emptiness();
	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf);
	cnfdf.merge(&cnf);

	do
	{
		Labelling prefcand = Labelling();
		cnfdf = SATFormulae(3 * this->af->numArgs());

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

			if (debug)
			{
				cout << endl;
				cout << "{";
				SetArgumentsIterator it;
				for (it = res.inargs()->begin(); it != res.inargs()->end();
						it++)
				{
					cout << (*it)->getName() << " ";
				}
				cout << "}" << endl;
			}

			//assignment of prefcand to the result of the SAT computation
			res.clone(&prefcand);

			if (res.undecargs()->empty())
			{
				break;
			}

			//reset cnfdf to TRUE
			cnfdf = SATFormulae(3 * this->af->numArgs());

			SetArgumentsIterator iter;
			for (iter = res.inargs()->begin(); iter != res.inargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(1, (*iter)->InVar()));
			}

			for (iter = res.outargs()->begin(); iter != res.outargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(1, (*iter)->OutVar()));
			}

			OrClause remainingIn = OrClause();
			OrClause remainingOut = OrClause();

			for (iter = res.undecargs()->begin();
					iter != res.undecargs()->end(); iter++)
			{
				if (this->conf->isInternalIn())
				{
					remainingIn.appendVariable((*iter)->InVar());
				}

				if (this->conf->isInternalOut())
				{
					remainingOut.appendVariable((*iter)->OutVar());
				}
			}

			if (this->conf->isInternalIn())
			{
				cnfdf.appendOrClause(remainingIn);
			}

			if (this->conf->isInternalOut())
			{
				cnfdf.appendOrClause(remainingOut);
			}

		} while (true);

		if (prefcand.empty())
			break;

		//decision problem
		if (arg != NULL)
		{
			if (prefcand.inargs()->exists(arg) == false)
				return false;
		}
		else
		{
			this->labellings.push_back(prefcand);
		}

		if (firstonly)
		{
			if (this->labellings.empty() && arg == NULL)
			{
				this->labellings.push_back(Labelling());
			}
			return true;
		}

		if (prefcand.inargs()->cardinality() == this->af->numArgs())
			break;

		OrClause oppsolution = OrClause();
		SetArgumentsIterator iter;
		if (this->conf->isExternalIn())
		{
			for (iter = prefcand.outargs()->begin();

			iter != prefcand.outargs()->end(); iter++)
			{
				oppsolution.appendVariable((*iter)->InVar());
			}
			cnf.appendOrClause(oppsolution);
		}

		if (this->conf->isExternalOut())
		{
			oppsolution = OrClause();
			for (iter = prefcand.inargs()->begin();
					iter != prefcand.inargs()->end(); iter++)
			{
				oppsolution.appendVariable((*iter)->OutVar());
			}
			cnf.appendOrClause(oppsolution);
		}

	} while (true);

	if (this->labellings.empty() && arg == NULL)
	{
		this->labellings.push_back(Labelling());
	}
	return true;
}

bool PreferredSemantics::credulousAcceptance(Argument *arg)
{
	return super::credulousAcceptance(arg);
}

bool PreferredSemantics::skepticalAcceptanceImproved(Argument *arg)
{
	this->cleanlabs();

	SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());
	SATFormulae cnfdf2 = SATFormulae(3 * this->af->numArgs());

	SATFormulae cnf1 = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf1);
	cnf1.appendOrClause(OrClause(1, arg->InVar()));
	Labelling res1 = Labelling();
	if (!this->satlab(cnf1, &res1))
	{
		return false;
	}

	SATFormulae cnf2 = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf2);
	cnf2.appendOrClause(OrClause(1, arg->OutVar()));
	Labelling res2 = Labelling();
	if (this->satlab(cnf2, &res2))
	{
		return false;
	}

	// non emptiness condition added -> at least one argument is IN.
	this->add_non_emptiness();
	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());
	this->sat_pigreek.clone(&cnf);

	do
	{
		Labelling maxcand = Labelling();
		cnfdf = SATFormulae(3 * this->af->numArgs());
		cnfdf2 = SATFormulae(3 * this->af->numArgs());
		cnfdf.appendOrClause(OrClause(1, arg->UndecVar()));

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

			//assignment of maxcand to the result of the SAT computation
			res.clone(&maxcand);

			// reset cnfdf2 to TRUE
			cnfdf2 = SATFormulae(3 * this->af->numArgs());

			SetArgumentsIterator iter;
			for (iter = res.inargs()->begin(); iter != res.inargs()->end(); iter++)
			{
				cnfdf2.appendOrClause(OrClause(1, (*iter)->InVar()));
			}

			for (iter = res.outargs()->begin(); iter != res.outargs()->end(); iter++)
			{
				cnfdf2.appendOrClause(OrClause(1, (*iter)->OutVar()));
			}

			// assign cnfdf
			cnfdf = SATFormulae(3 * this->af->numArgs());
			cnfdf.appendOrClause(OrClause(1, arg->UndecVar()));
			cnfdf2.merge(&cnfdf);

			OrClause remainingIn = OrClause();
			OrClause remainingOut = OrClause();

			for (iter = res.undecargs()->begin(); iter != res.undecargs()->end(); iter++)
			{
				if (this->conf->isInternalIn())
				{
					if((*iter)->getName().compare(arg->getName()) != 0)
						remainingIn.appendVariable((*iter)->InVar());
				}

				if (this->conf->isInternalOut())
				{
					if((*iter)->getName().compare(arg->getName()) != 0)
						remainingOut.appendVariable((*iter)->OutVar());
				}
			}

			if (this->conf->isInternalIn())
			{
				cnfdf.appendOrClause(remainingIn);
			}

			if (this->conf->isInternalOut())
			{
				cnfdf.appendOrClause(remainingOut);
			}

		} while (true);

		if (maxcand.empty())
			break;

		SATFormulae cnf_comp = SATFormulae(3 * this->af->numArgs());
		cnf.clone(&cnf_comp);
		cnfdf2.merge(&cnf_comp);
		cnf_comp.appendOrClause(OrClause(1, arg->InVar()));

		Labelling res3 = Labelling();
		if(!this->satlab(cnf_comp, &res3))
		{
			return false;
		}

		OrClause oppsolution = OrClause();
		SetArgumentsIterator iter;
		if (this->conf->isExternalIn())
		{
			for (iter = maxcand.outargs()->begin(); iter != maxcand.outargs()->end(); iter++)
			{
				if((*iter)->getName().compare(arg->getName()) != 0)
					oppsolution.appendVariable((*iter)->InVar());
			}
			cnf.appendOrClause(oppsolution);
		}

		if (this->conf->isExternalOut())
		{
			oppsolution = OrClause();
			for (iter = maxcand.inargs()->begin(); iter != maxcand.inargs()->end(); iter++)
			{
				if((*iter)->getName().compare(arg->getName()) != 0)
					oppsolution.appendVariable((*iter)->OutVar());
			}
			cnf.appendOrClause(oppsolution);
		}

	} while (true);

	return true;
}

bool PreferredSemantics::skepticalAcceptance(Argument *arg)
{
	if(this->conf->isImprovedUsed())
	{
		return this->skepticalAcceptanceImproved(arg);
	}
	else
	{
		if (this->credulousAcceptance(arg) == false)
				return false;
			return this->compute(arg);
	}
	return NULL;
}

SetArguments *PreferredSemantics::someExtension()
{
	this->compute(NULL, true);
	return this->labellings.at(0).inargs();
}

PreferredSemantics::~PreferredSemantics()
{
	// TODO Auto-generated destructor stub
}

