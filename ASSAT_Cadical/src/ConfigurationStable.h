#include <string>
#include <exception>
#include <array>

using namespace std;

#ifndef SRC_CONFIGURATIONSTABLE_H_
#define SRC_CONFIGURATIONSTABLE_H_

#define STABLECONFPOS		5

#define POS_ALLSAT	0
#define POS_IN 		1
#define POS_OUT		2
#define POS_DC_IMPR	3
#define POS_DS_IMPR	4

/**
 * @class ConfigurationCompleteLengthException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not 2 characters long
 */
class ConfigurationStableLengthException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Stable Length Exception";
	}
};

/**
 * @class ConfigurationCompleteException
 * Exception raised if the string passed to
 * #ConfigurationComplete:#ConfigurationComplete is not acceptable
 */
class ConfigurationStableException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Stable Exception";
	}
};

class ConfigurationStable
{
	array<bool, STABLECONFPOS> conf;
	bool check();

public:
	ConfigurationStable(string);
	virtual ~ConfigurationStable();

	bool isIn() const
	{
		return this->conf[POS_IN];
	}

	bool isOut() const
	{
		return this->conf[POS_OUT];
	}

	bool allSat() const
	{
		return this->conf[POS_ALLSAT];
	}

	bool isDCImpr() const
	{
		return this->conf[POS_DC_IMPR];
	}

	bool isDSImpr() const
	{
		return this->conf[POS_DS_IMPR];
	}

};

#endif /* SRC_CONFIGURATIONSTABLE_H_ */
