/**
 * @file 		CompleteSemantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */


#ifndef COMPLETESEMANTICS_H_
#define COMPLETESEMANTICS_H_

#include "ConfigurationComplete.h"
#include "Semantics.h"

/**
 * @class ConfigurationCompleteLengthException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not 2 characters long
 */
class AllSATException: public exception
{
	virtual const char* what() const throw ()
	{
		return "AllSAT can be used only to enumerate all the extensions";
	}
};

class CompleteSemantics: public Semantics
{
	typedef Semantics super;
protected:
	void add_some_undec();
	ConfigurationComplete *conf;
public:
	/**
	 * @see Semantics#Semantics
	 */
	CompleteSemantics(AF *the_af, Encoding enc, ConfigurationComplete *c) :
			super(the_af, enc)
	{
		this->conf = c;
	}
	;
	bool credulousAcceptance(Argument *arg);
	bool skepticalAcceptance(Argument *arg);
	virtual ~CompleteSemantics();
	bool compute(Argument *arg = NULL, bool firstonly=false);
	SetArguments *someExtension();
};

#endif /* COMPLETESEMANTICS_H_ */
