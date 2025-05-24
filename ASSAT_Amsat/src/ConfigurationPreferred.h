/*
 * PreferredConfiguration.h
 *
 *  Created on: 13 Jun 2016
 *      Author: geryo
 */

#include <string>
#include <exception>
#include <array>


using namespace std;


#ifndef SRC_PREFERREDCONFIGURATION_H_
#define SRC_PREFERREDCONFIGURATION_H_

#define PREFCONFPOS		6

#define POS_INT_IN 		0
#define POS_INT_OUT		1
#define POS_EXT_IN	 	2
#define POS_EXT_OUT  	3
#define POS_STABLE	 	4
#define POS_IMPROVED 	5

/**
 * @class ConfigurationPreferredLengthException
 * Exception raised if the string passed to
 * #ConfigurationPreferred:#ConfigurationPreferred is not 5 characters long
 */
class ConfigurationPreferredLengthException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Preferred Length Exception";
	}
};

/**
 * @class ConfigurationPreferredException
 * Exception raised if the string passed to
 * #ConfigurationPreferred:#ConfigurationPreferred is not acceptable
 */
class ConfigurationPreferredException: public exception
{
	virtual const char* what() const throw ()
	{
		return "Configuration Preferred Exception";
	}
};

class ConfigurationPreferred
{
private:

	array<bool, PREFCONFPOS> conf;
	bool check();

public:
	ConfigurationPreferred();
	ConfigurationPreferred(string);
	virtual ~ConfigurationPreferred();


	bool isExternalIn() const
	{
		return this->conf[POS_EXT_IN];
	}

	bool isExternalOut() const
	{
		return this->conf[POS_EXT_OUT];
	}

	bool isInternalIn() const
	{
		return this->conf[POS_INT_IN];
	}

	bool isInternalOut() const
	{
		return this->conf[POS_INT_OUT];
	}

	bool isStableUsed() const
	{
		return this->conf[POS_STABLE];
	}

	bool isImprovedUsed() const
		{
			return this->conf[POS_IMPROVED];
		}
};

#endif /* SRC_PREFERREDCONFIGURATION_H_ */
