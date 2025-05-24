#include <string>
#include <exception>
#include <array>

using namespace std;


#ifndef SRC_CONFIGURATIONCOMPLETE_H_
#define SRC_CONFIGURATIONCOMPLETE_H_

#define COMPLETECONFPOS		1

#define POS_ALLSAT	0

/**
 * @class ConfigurationCompleteLengthException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not 2 characters long
 */
class ConfigurationCompleteLengthException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration complete Length Exception";
	}
};

/**
 * @class ConfigurationCompleteException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not acceptable
 */
class ConfigurationCompleteException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Complete Exception";
	}
};


class ConfigurationComplete
{
	array<bool, COMPLETECONFPOS> conf;
	bool check();


public:
	ConfigurationComplete(string c);
	virtual ~ConfigurationComplete();

	bool allSat() const
	{
		return this->conf[POS_ALLSAT];
	}

};

#endif /* SRC_CONFIGURATIONCOMPLETE_H_ */
