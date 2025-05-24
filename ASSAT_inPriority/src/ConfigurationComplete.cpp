/*
 * ConfigurationComplete.cpp
 *
 *  Created on: 16 Jun 2016
 *      Author: geryo
 */

#include <ConfigurationComplete.h>


bool ConfigurationComplete::check()
{
	return true;

}

ConfigurationComplete::ConfigurationComplete(string c)
{
	if (c.length() != COMPLETECONFPOS)
			throw ConfigurationCompleteLengthException();

		int j = 0;
		for (string::iterator it = c.begin(); it != c.end(); it++)
		{
			this->conf[j++] = *(it) - '0';
		}
		if (!this->check())
		{
			throw ConfigurationCompleteException();
		}

}

ConfigurationComplete::~ConfigurationComplete()
{
	// TODO Auto-generated destructor stub
}

