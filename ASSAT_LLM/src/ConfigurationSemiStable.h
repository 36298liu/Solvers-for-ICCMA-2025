#include <string>
#include <exception>
#include <array>

using namespace std;

#ifndef SRC_CONFIGURATIONSEMISTABLE_H_
#define SRC_CONFIGURATIONSEMISTABLE_H_

#define SEMISTABLECONFPOS		2

#define POS_ALLSAT	 		0
#define POS_OLDVERSION		1

/**
 * @class ConfigurationCompleteLengthException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not 2 characters long
 */
class ConfigurationSemiStableLengthException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Semi-Stable Length Exception";
	}
};

/**
 * @class ConfigurationCompleteException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not acceptable
 */
class ConfigurationSemiStableException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Semi-Stable Exception";
	}
};

class ConfigurationSemiStable
{
	array<bool, SEMISTABLECONFPOS> conf;
	bool check();

public:
	ConfigurationSemiStable(string);
	virtual ~ConfigurationSemiStable();

	bool allSat() const
	{
		return this->conf[POS_ALLSAT];
	}

	bool oldVersion() const
	{
		return this->conf[POS_OLDVERSION];
	}

};

#endif /* SRC_CONFIGURATIONSEMISTABLE_H_ */
