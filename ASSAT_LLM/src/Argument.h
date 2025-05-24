/**
 * @file 		Argument.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */


#ifndef ARGUMENT_H_
#define ARGUMENT_H_

#include <string>
using namespace std;


class AF;
class SetArguments;
/**
 * @class Variable Argument.h Argument.h
 * @brief `Variable` is defined easily as a `typedef int Variable`
 */
typedef int Variable;

/**
 * @def NOT(x)
 * @brief	Computes the negation of `Variable` x
 */
#define NOT(x) (-x)


class Argument
{
	string name;
	int number;
	AF *af;
	SetArguments *attacks;
	SetArguments *attackers;
public:
	Argument(string, int, AF*);
	virtual ~Argument();
	string getName() const;
	int getNumber() const;
	AF *get_af();
	Variable InVar();
	Variable OutVar();
	Variable UndecVar();
	Variable NotInVar();
	Variable NotOutVar();
	Variable NotUndecVar();
	bool operator==(const Argument &other) const;
	bool operator!=(const Argument &other) const;
	void add_attacks(Argument *);
	void add_attackers(Argument *);
	SetArguments *get_attacks();
	SetArguments *get_attackers();
};

#ifndef GRAPH_H_
#include "AF.h"
#include "SetArguments.h"
#endif


#endif /* ARGUMENT_H_ */
