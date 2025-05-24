/**
 * @file 		StableSemantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef STABLESEMANTICS_H_
#define STABLESEMANTICS_H_

#include "CompleteSemantics.h"

/**
 * @class AllSATStableException
 */
class AllSATStableException: public exception
{
	virtual const char* what() const throw ()
	{
		return "AllSAT can be used only to enumerate all the extensions";
	}
};


class StableSemantics: public Semantics
{
	ConfigurationStable *conf;
	typedef Semantics super;
public:
	bool compute(Argument *arg = NULL, bool firstonly = false);
	bool credulousAcceptance(Argument *arg);
	bool credulousAcceptanceComplete(Argument *arg);
	bool skepticalAcceptance(Argument *arg);

	bool credulousAcceptanceImproved(Argument *arg);
	bool skepticalAcceptanceImproved(Argument *arg);
	SetArguments *someExtension();
	/**
	 * @see CompleteSemantics#CompleteSemantics
	 */
	StableSemantics(AF *the_af, Encoding enc, ConfigurationStable *c) :
			super(the_af, enc)
	{
		this->conf = c;
		for (SetArgumentsIterator arg = this->af->begin(); arg != this->af->end(); arg++)
					this->sat_pigreek.appendOrClause(OrClause(1, (*arg)->NotUndecVar()));
	}
	;

	virtual ~StableSemantics();
};

#endif /* STABLESEMANTICS_H_ */
