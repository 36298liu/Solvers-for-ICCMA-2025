/*
 * PreferredConfiguration.cpp
 *
 *  Created on: 13 Jun 2016
 *      Author: geryo
 */

#include <ConfigurationPreferred.h>

bool ConfigurationPreferred::check()
{
	if (this->isInternalIn() == false && this->isInternalOut() == false)
		return false;

	if (this->isExternalIn() == false && this->isExternalOut() == false)
		return false;

	return true;
}

ConfigurationPreferred::ConfigurationPreferred()
{
	// TODO Auto-generated constructor stub

}

/**
 * @brief			Constructor for a Preferred Configuration
 * @param[in] c		Input string representing booleans about IN argument / OUT argument in internal cycle; IN argument / OUT argument in external cycle; use of stable
 *	                TODO documentation
 * 	@throws			ConfigurationPreferredLengthException
 * 	@throws			ConfigurationPreferredException
 */
ConfigurationPreferred::ConfigurationPreferred(string c)
{
	if (c.length() != PREFCONFPOS)
		throw ConfigurationPreferredLengthException();

	int j = 0;
	for (string::iterator it = c.begin(); it != c.end(); it++)
	{
		this->conf[j++] = *(it) - '0';
	}
	if (!this->check())
	{
		throw ConfigurationPreferredException();
	}
}

ConfigurationPreferred::~ConfigurationPreferred()
{
	// TODO Auto-generated destructor stub
}

