/**
 * @file 		SemistableSemantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef SEMISTABLESEMANTICS_H_
#define SEMISTABLESEMANTICS_H_

#include "Semantics.h"
#include "StableSemantics.h"

#include "ConfigurationSemiStable.h"

class SemistableSemantics: public Semantics
{
	ConfigurationStable *confStable;
	ConfigurationSemiStable *conf;
	typedef Semantics super;
//protected:
	//double timeAllSat = 0;
	//double timeInternalDoWhile = 0;
public:
	//double getTimeAllSat();
	//double getTimeInternalDoWhile();
	bool compute(Argument *arg = NULL, bool firstonly = false);
	bool credulousAcceptance(Argument *arg);
	bool skepticalAcceptance(Argument *arg);
	SetArguments *someExtension();
	/**
	 * @see CompleteSemantics#CompleteSemantics
	 */
	SemistableSemantics(AF *the_af, Encoding enc, ConfigurationStable *cStable, ConfigurationSemiStable *c) :
			super(the_af, enc)
	{
		this->confStable = cStable;
		this->conf = c;
	}
	;
	virtual ~SemistableSemantics();
};

#endif /* SEMISTABLESEMANTICS_H_ */
