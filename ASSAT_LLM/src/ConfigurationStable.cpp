/*
 * ConfigurationStable.cpp
 *
 *  Created on: 14 Jun 2016
 *      Author: geryo
 */

#include <ConfigurationStable.h>

bool ConfigurationStable::check()
{
	if (!this->allSat() && this->isIn() == false && this->isOut() == false)
		return false;

	return true;
}

/**
 * @brief			Constructor for a Complete Configuration
 * @param[in] c		Input string representing booleans about IN argument / OUT argument
 *	                TODO documentation
 * 	@throws			ConfigurationCompleteLengthException
 * 	@throws			ConfigurationCompleteException
 */
ConfigurationStable::ConfigurationStable(string c)
{
	if (c.length() != STABLECONFPOS)
		throw ConfigurationStableLengthException();

	int j = 0;
	for (string::iterator it = c.begin(); it != c.end(); it++)
	{
		this->conf[j++] = *(it) - '0';
	}
	if (!this->check())
	{
		throw ConfigurationStableException();
	}

}

ConfigurationStable::~ConfigurationStable()
{
	// TODO Auto-generated destructor stub
}

