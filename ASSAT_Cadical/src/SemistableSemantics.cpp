/**
 * @file 		SemistableSemantics.cpp
 * @class 		SemistableSemantics
 * @brief 		Class for the semi stable semantics
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "SemistableSemantics.h"

// Library for calculation of AllSAT/inner do-while times
//#include <ctime>

/**
 * @brief Computing semantics extensions
 */

bool SemistableSemantics::compute(Argument *arg, bool firstonly)
{
	this->cleanlabs();

	StableSemantics stabSem = StableSemantics(af, encoding, confStable);

	if (firstonly)
		stabSem.compute(NULL, true);
	else
		stabSem.compute();

	if(stabSem.getLabellings().empty() == false && arg == NULL)
	{
		this->labellings = stabSem.getLabellings();
	}
	else
	{
		this->add_non_emptiness();
		this->cleanlabs();

		SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

		SATFormulae cnf = SATFormulae(3 * this->af->numArgs());

		// Time spent by the inner do-while in milliseconds
		//timeAllSat = 0;
		//timeInternalDoWhile = 0;

		this->sat_pigreek.clone(&cnf);
		do
		{
			Labelling semistabcand = Labelling();
			cnfdf = SATFormulae(3 * this->af->numArgs());

			//clock_t start_t1=clock();

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

				//assignment of semistabcand to the result of the SAT computation
				res.clone(&semistabcand);

				//reset cnfdf to TRUE
				cnfdf = SATFormulae(3 * this->af->numArgs());

				SetArgumentsIterator iter;
				for (iter = res.inargs()->begin(); iter != res.inargs()->end();
						iter++)
				{
					cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
				}

				for (iter = res.outargs()->begin(); iter != res.outargs()->end();
						iter++)
				{
					cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
				}

				OrClause remaining = OrClause();

				for (iter = res.undecargs()->begin(); iter != res.undecargs()->end(); iter++)
				{
					remaining.appendVariable((*iter)->NotUndecVar());
				}

				cnfdf.appendOrClause(remaining);

			} while (true);

			//clock_t stop_t1=clock();
			//timeInternalDoWhile += (stop_t1-start_t1)/double(CLOCKS_PER_SEC);

			if (semistabcand.empty())
				break;

			this->labellings.push_back(semistabcand);

			if (firstonly && arg == NULL)
			{
				if (this->labellings.empty() && arg == NULL)
				{
					this->labellings.push_back(Labelling());
				}
				return true;
			}

			OrClause oppsolution = OrClause();
			SetArgumentsIterator iter;

			if(this->conf->oldVersion())
			{
				// METHOD 1

				// (At least one UNDEC turns IN/OUT) OR (Every IN/OUT is IN OR OUT)
				// AND (at least 1 semistabcand elements has to change) move to another research space at the next iteration
				OrClause notSemistabcand = OrClause();

				// Boolean operations
				// ((a OR b OR C…) OR (w AND r AND t…) turns to be
				// (a OR b OR c OR … OR w) AND (a OR b OR c OR … OR r) AND (a OR b OR c OR … OR t) …)

				// (At least one UNDEC turns to be IN/OUT), in format (a OR b OR c...)
				OrClause undecToNotUndec = OrClause();
				for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
				{
					undecToNotUndec.appendVariable((*iter)->NotUndecVar());

					notSemistabcand.appendVariable((*iter)->NotUndecVar());
				}

				// (Every IN/OUT is IN OR OUT)
				for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
				{
					OrClause undecToNotUndec_appendable = OrClause();
					undecToNotUndec.clone(&undecToNotUndec_appendable);
					undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

					cnf.appendOrClause(undecToNotUndec_appendable);

					notSemistabcand.appendVariable((*iter)->NotInVar());
				}
				for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
				{
					OrClause undecToNotUndec_appendable = OrClause();
					undecToNotUndec.clone(&undecToNotUndec_appendable);
					undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

					cnf.appendOrClause(undecToNotUndec_appendable);

					notSemistabcand.appendVariable((*iter)->NotOutVar());
				}
				cnf.appendOrClause(notSemistabcand);
			}
			else
			{
				// METHOD 2

				SATFormulae allUndec = SATFormulae(3 * this->af->numArgs());
				for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
				{
					allUndec.appendOrClause(OrClause(1, (*iter)->UndecVar()));
				}

				SATFormulae inOrOut = SATFormulae(3 * this->af->numArgs());
				for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
				{
					inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
				}
				for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
				{
					inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
				}

				SATFormulae complete_cnf = SATFormulae(3 * this->af->numArgs());
				cnf.clone(&complete_cnf);
				allUndec.merge(&complete_cnf);
				inOrOut.merge(&complete_cnf);


				vector<Labelling> labellingsComplete = vector<Labelling>();
				if(this->conf->allSat())
				{
					// AllSAT execution, time is measured and added up to the overall
					//clock_t start_t=clock();

					this->allsat(complete_cnf, &(labellingsComplete), NULL, NULL, -1);

					//clock_t stop_t=clock();
					//timeAllSat += (stop_t-start_t)/double(CLOCKS_PER_SEC);

					iterator it;
					for( it = labellingsComplete.begin(); it != labellingsComplete.end(); ++it)
					{
						// duplicate extension not inserted
						if ((*it).getIn().operator ==(semistabcand.getIn()) == false)
						{
							this->labellings.push_back((*it));
						}
					}
				}
				else
				{
					SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

					do
					{
						Labelling res = Labelling();

						SATFormulae cnf_AND_cnfdf = SATFormulae(3 * this->af->numArgs());
						complete_cnf.clone(&cnf_AND_cnfdf);
						cnfdf.merge(&cnf_AND_cnfdf);

						if (!this->satlab(cnf_AND_cnfdf, &res))
						{
							break;
						}

						if(res.getIn().operator ==(semistabcand.getIn()) == false)
						{
							this->labellings.push_back(res);
						}

						OrClause oppsolution = OrClause();

						for (SetArgumentsIterator arg = res.inargs()->begin(); arg != res.inargs()->end(); arg++)
						{
							oppsolution.appendVariable((*arg)->NotInVar());
						}

						for (SetArgumentsIterator arg = res.outargs()->begin(); arg != res.outargs()->end(); arg++)
						{
							oppsolution.appendVariable((*arg)->NotOutVar());
						}

						for (SetArgumentsIterator arg = res.undecargs()->begin(); arg != res.undecargs()->end(); arg++)
						{
							oppsolution.appendVariable((*arg)->NotUndecVar());
						}

						cnfdf.appendOrClause(oppsolution);

					} while (true);
				}


				OrClause undecToNotUndec = OrClause();
				for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
				{
					undecToNotUndec.appendVariable((*iter)->NotUndecVar());
				}
				cnf.appendOrClause(undecToNotUndec);
			}
		} while (true);

		if (this->labellings.empty())
		{
			this->labellings.push_back(Labelling());
		}
	}
	return true;
}

/*double SemistableSemantics::getTimeAllSat()
{
	return timeAllSat;
}
double SemistableSemantics::getTimeInternalDoWhile()
{
	return timeInternalDoWhile;
}*/

SetArguments *SemistableSemantics::someExtension()
{
	this->compute(NULL, true);
	if (this->labellings.empty() || (this->labellings.empty() && this->af->numArgs() != 0))
		return NULL;
	else
		return this->labellings.at(0).inargs();
}

bool SemistableSemantics::credulousAcceptance(Argument *arg)
{
	this->cleanlabs();
	StableSemantics stabSem = StableSemantics(af, encoding, confStable);

	int acceptance = stabSem.credulousAcceptanceImproved(arg);
	if(acceptance != -1)
		return acceptance;

	this->add_non_emptiness();
	this->cleanlabs();

	SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());

	this->sat_pigreek.clone(&cnf);
	do
	{
		Labelling semistabcand = Labelling();
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

			//assignment of semistabcand to the result of the SAT computation
			res.clone(&semistabcand);

			//reset cnfdf to TRUE
			cnfdf = SATFormulae(3 * this->af->numArgs());

			SetArgumentsIterator iter;
			for (iter = res.inargs()->begin(); iter != res.inargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			for (iter = res.outargs()->begin(); iter != res.outargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			OrClause remaining = OrClause();

			for (iter = res.undecargs()->begin(); iter != res.undecargs()->end(); iter++)
			{
				remaining.appendVariable((*iter)->NotUndecVar());
			}

			cnfdf.appendOrClause(remaining);

		} while (true);

		if (semistabcand.empty())
			break;

		if (semistabcand.inargs()->exists(arg))
						return true;

		OrClause oppsolution = OrClause();
		SetArgumentsIterator iter;

		if(this->conf->oldVersion())
		{
			// METHOD 1

			OrClause notSemistabcand = OrClause();
			OrClause undecToNotUndec = OrClause();
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				undecToNotUndec.appendVariable((*iter)->NotUndecVar());

				notSemistabcand.appendVariable((*iter)->NotUndecVar());
			}

			for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
			{
				OrClause undecToNotUndec_appendable = OrClause();
				undecToNotUndec.clone(&undecToNotUndec_appendable);
				undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

				cnf.appendOrClause(undecToNotUndec_appendable);

				notSemistabcand.appendVariable((*iter)->NotInVar());
			}
			for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
			{
				OrClause undecToNotUndec_appendable = OrClause();
				undecToNotUndec.clone(&undecToNotUndec_appendable);
				undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

				cnf.appendOrClause(undecToNotUndec_appendable);

				notSemistabcand.appendVariable((*iter)->NotOutVar());
			}
			cnf.appendOrClause(notSemistabcand);
			cnf.appendOrClause(OrClause(1, (arg)->InVar()));

			Labelling res_temp = Labelling();
			if (this->satlab(cnf, &res_temp))
				return true;
			else
				return false;
		}
		else
		{
			// METHOD 2

			SATFormulae allUndec = SATFormulae(3 * this->af->numArgs());
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				allUndec.appendOrClause(OrClause(1, (*iter)->UndecVar()));
			}

			SATFormulae inOrOut = SATFormulae(3 * this->af->numArgs());
			for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
			{
				inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}
			for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
			{
				inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			SATFormulae complete_cnf = SATFormulae(3 * this->af->numArgs());
			cnf.clone(&complete_cnf);
			allUndec.merge(&complete_cnf);
			inOrOut.merge(&complete_cnf);

			//DC
			complete_cnf.appendOrClause(OrClause(1, (arg)->InVar()));

			Labelling res_temp = Labelling();
			if (this->satlab(complete_cnf, &res_temp))
				return true;

			OrClause undecToNotUndec = OrClause();
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				undecToNotUndec.appendVariable((*iter)->NotUndecVar());
			}
			cnf.appendOrClause(undecToNotUndec);
		}
	} while (true);

	return false;
}

bool SemistableSemantics::skepticalAcceptance(Argument *arg)
{
	this->cleanlabs();
	StableSemantics stabSem = StableSemantics(af, encoding, confStable);

	int acceptance = stabSem.skepticalAcceptanceImproved(arg);
	if(acceptance != -1)
		return acceptance;

	this->add_non_emptiness();
	this->cleanlabs();

	SATFormulae cnfdf = SATFormulae(3 * this->af->numArgs());

	SATFormulae cnf = SATFormulae(3 * this->af->numArgs());

	this->sat_pigreek.clone(&cnf);

	Labelling res_sol_check = Labelling();
	if (!this->satlab(cnf, &res_sol_check))
	{
		return false;
	}

	do
	{
		Labelling semistabcand = Labelling();
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

			if (!res.inargs()->exists(arg))
						return false;

			//assignment of semistabcand to the result of the SAT computation
			res.clone(&semistabcand);

			//reset cnfdf to TRUE
			cnfdf = SATFormulae(3 * this->af->numArgs());

			SetArgumentsIterator iter;
			for (iter = res.inargs()->begin(); iter != res.inargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			for (iter = res.outargs()->begin(); iter != res.outargs()->end();
					iter++)
			{
				cnfdf.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			OrClause remaining = OrClause();

			for (iter = res.undecargs()->begin(); iter != res.undecargs()->end(); iter++)
			{
				remaining.appendVariable((*iter)->NotUndecVar());
			}

			cnfdf.appendOrClause(remaining);

		} while (true);

		if (semistabcand.empty())
			break;

		OrClause oppsolution = OrClause();
		SetArgumentsIterator iter;

		if(this->conf->oldVersion())
		{

			// METHOD 1

			OrClause notSemistabcand = OrClause();

			OrClause undecToNotUndec = OrClause();
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				undecToNotUndec.appendVariable((*iter)->NotUndecVar());

				notSemistabcand.appendVariable((*iter)->NotUndecVar());
			}

			for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
			{
				OrClause undecToNotUndec_appendable = OrClause();
				undecToNotUndec.clone(&undecToNotUndec_appendable);
				undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

				cnf.appendOrClause(undecToNotUndec_appendable);

				notSemistabcand.appendVariable((*iter)->NotInVar());
			}
			for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
			{
				OrClause undecToNotUndec_appendable = OrClause();
				undecToNotUndec.clone(&undecToNotUndec_appendable);
				undecToNotUndec_appendable.appendVariable((*iter)->NotUndecVar());

				cnf.appendOrClause(undecToNotUndec_appendable);

				notSemistabcand.appendVariable((*iter)->NotOutVar());
			}
			cnf.appendOrClause(notSemistabcand);
						cnf.appendOrClause(OrClause(1, (arg)->OutVar()));

						Labelling res_temp = Labelling();
						if (this->satlab(cnf, &res_temp))
							return false;
						else
							return true;
		}
		else
		{
			// METHOD 2

			SATFormulae allUndec = SATFormulae(3 * this->af->numArgs());
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				allUndec.appendOrClause(OrClause(1, (*iter)->UndecVar()));
			}

			SATFormulae inOrOut = SATFormulae(3 * this->af->numArgs());
			for (iter = semistabcand.inargs()->begin(); iter != semistabcand.inargs()->end(); iter++)
			{
				inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}
			for (iter = semistabcand.outargs()->begin(); iter != semistabcand.outargs()->end(); iter++)
			{
				inOrOut.appendOrClause(OrClause(2, (*iter)->InVar(), (*iter)->OutVar()));
			}

			SATFormulae complete_cnf = SATFormulae(3 * this->af->numArgs());
			cnf.clone(&complete_cnf);
			allUndec.merge(&complete_cnf);
			inOrOut.merge(&complete_cnf);

			//DS
			complete_cnf.appendOrClause(OrClause(1, (arg)->OutVar()));

			Labelling res_temp = Labelling();
			if (this->satlab(complete_cnf, &res_temp))
				return false;

			OrClause undecToNotUndec = OrClause();
			for (iter = semistabcand.undecargs()->begin(); iter != semistabcand.undecargs()->end(); iter++)
			{
				undecToNotUndec.appendVariable((*iter)->NotUndecVar());
			}
			cnf.appendOrClause(undecToNotUndec);
		}
	} while (true);

	return true;
}

SemistableSemantics::~SemistableSemantics()
{
	// TODO Auto-generated destructor stub
}

