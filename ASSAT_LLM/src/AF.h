/**
 * @file 		AF.h
 * @author 		Mauro Vallati <m.vallati@hud.ac.uk>
 * @copyright	MIT
 */

#ifndef GRAPH_H_
#define GRAPH_H_

#include <map>
#include <fstream>
#include <iostream>


#include "Argument.h"
class SetArguments;
class SetArgumentsIterator;

extern bool debug;


using namespace std;

class AF
{
	SetArguments *arguments;
	//vector<pair<int, int> > raw_attacks;
	//map<Argument *, SetArguments *> attacks;
	//map<Argument *, SetArguments *> attackers;
	string trim(string);
public:
	AF();
	virtual ~AF();
	bool readFile(string file);
	int numArgs();
	Argument *getArgumentByName(string);
	Argument *getArgumentByNumber(int position);
	SetArguments *get_arguments() const;
	SetArgumentsIterator begin();
	SetArgumentsIterator end();
};

#include "SetArguments.h"

#endif /* GRAPH_H_ */
