/**
 * @file 		GroundedSemantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef GROUNDEDSEMANTICS_H_
#define GROUNDEDSEMANTICS_H_

#include "Semantics.h"

class GroundedSemantics: public Semantics
{
	typedef Semantics super;
public:
	bool compute(Argument *arg = NULL, bool firstonly = false);
	bool credulousAcceptance(Argument *arg);
	bool skepticalAcceptance(Argument *arg);
	SetArguments *someExtension();
	/**
	 * @see CompleteSemantics#CompleteSemantics
	 */
	GroundedSemantics(AF *the_af, Encoding enc) :
			super(the_af, enc)
	{
	}
	;
	virtual ~GroundedSemantics();
};

#endif /* GROUNDEDSEMANTICS_H_ */
