/**
 * @file 		PreferredSemantics.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#ifndef PREFERREDSEMANTICS_H_
#define PREFERREDSEMANTICS_H_

#include <ConfigurationStable.h>
#include "ConfigurationPreferred.h"
#include "Semantics.h"

/**
 * @class ConfigurationCompleteLengthException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not 2 characters long
 */
class ConfigurationPreferredExperimental: public exception
{
	virtual const char* what() const throw ()
	{
		return "Please do not use ALLSAT with preferred";
	}
};

class PreferredSemantics: public Semantics
{

protected:
	ConfigurationPreferred *conf;
	ConfigurationStable *confStable;

	typedef Semantics super;

public:
	PreferredSemantics(AF *the_af, Encoding enc, ConfigurationPreferred*, ConfigurationStable*);
	virtual ~PreferredSemantics();
	bool compute(Argument *arg = NULL, bool firstonly = false);
	bool credulousAcceptance(Argument *arg);
	bool skepticalAcceptance(Argument *arg);
	bool skepticalAcceptanceImproved(Argument *arg);

	SetArguments *someExtension();

};

#endif /* PREFERREDSEMANTICS_H_ */
