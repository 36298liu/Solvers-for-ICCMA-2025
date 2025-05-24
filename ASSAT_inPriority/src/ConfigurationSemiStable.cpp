/*
 * ConfigurationSemiStable.cpp
 *
 *  Created on: 12 Oct 2016
 *      Author: tobia
 */

#include <ConfigurationSemiStable.h>

bool ConfigurationSemiStable::check()
{
	return true;
}

/**
 * @brief			Constructor for a Complete Configuration
 * @param[in] c		Input string representing booleans about IN argument / OUT argument
 *	                TODO documentation
 * 	@throws			ConfigurationCompleteLengthException
 * 	@throws			ConfigurationCompleteException
 */
ConfigurationSemiStable::ConfigurationSemiStable(string c)
{
	if (c.length() != SEMISTABLECONFPOS)
		throw ConfigurationSemiStableLengthException();

	int j = 0;
	for (string::iterator it = c.begin(); it != c.end(); it++)
	{
		this->conf[j++] = *(it) - '0';
	}
	if (!this->check())
	{
		throw ConfigurationSemiStableException();
	}

}

ConfigurationSemiStable::~ConfigurationSemiStable()
{
	// TODO Auto-generated destructor stub
}

