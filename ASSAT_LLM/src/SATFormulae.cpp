/**
 * @file 		SATFormulae.cpp
 * @class 		SATFormulae
 * @brief 		Class encompassing a list of `OrClause` linked by and operators
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include "SATFormulae.h"
#include <stdexcept>
#include "fastformat/fastformat.h"
#include "fastformat/inserters/to_i.hpp"
#include "fastformat/sinks/ostream.hpp"
#include "fastformat/ff.hpp"

/**
 * @brief	Simple constructor
 */
SATFormulae::SATFormulae(long numvar)
{
	this->clauses_and = vector<OrClause>();
	this->numvar = numvar;
}

SATFormulae::SATFormulae()
{
	this->clauses_and = vector<OrClause>();
	this->numvar = -1;
}

void SATFormulae::setNumVar(long l)
{
	this->numvar = l;
}

/**
 * @brief		Method for appending a new OrClause to the other clause
 * @param[in] c	The OrClause to append
 * @retval void
 */
void SATFormulae::appendOrClause(OrClause c)
{
	this->clauses_and.push_back(c);
}

/**
 * @brief			Method for transforming the SAT formulae into a string `DIMACS` compliant
 * @param[out] ss	A pointer to a stringstream object already initialised
 * @retval void
 */
void SATFormulae::toSS(stringstream *ss) const
{
	(*ss) << this->toString();
}

string SATFormulae::toString() const
{
	if (this->numvar == -1)
		throw runtime_error("number of variables unspecified");

	string newline = "\n";
	string ret = "p cnf ";
	fastformat::write(ret, this->numvar);
	ret += " ";
	fastformat::write(ret, this->size());
	ret += newline;

	for (int i = 0; i < (int) this->clauses_and.size(); i++)
	{
		if (!this->clauses_and.at(i).isEmpty())
		{
			ret += this->clauses_and.at(i).toString();
			if (i != (int) this->clauses_and.size() - 1)
				ret += newline;
		}
	}
	return ret;
}

ostream& operator<<(ostream& out, const SATFormulae& r)
{
	out << r.toString();
	return out;
}

/**
 * @brief 		Method returning the number of OrClause
 * @retval int	The number of OrClause
 */
int SATFormulae::size() const
{
	return (int) this->clauses_and.size();
}

/**
 * @brief 				Method for cloning (not coping the pointers) this object into a new one
 * @param[out] newsat	A pointer to an initialised SATFormulae() object which will contain the copy of this object
 * @retval void
 */
void SATFormulae::clone(SATFormulae *newsat)
{
	(*newsat) = SATFormulae(this->numvar);
	for (int i = 0; i < this->size(); i++)
	{
		OrClause newor = OrClause();
		this->clauses_and.at(i).clone(&newor);
		(*newsat).appendOrClause(newor);
	}

}

void SATFormulae::merge(SATFormulae *newsat)
{
	for (vector<OrClause>::iterator iter = this->clauses_and.begin(); iter != this->clauses_and.end(); iter++)
	{
		newsat->appendOrClause((*iter));
	}
}

/**
 * @brief 	Check if there are no formulae
 * @retval bool
 */
bool SATFormulae::empty()
{
	return this->clauses_and.empty();
}

SATFormulae::~SATFormulae()
{

}

long SATFormulae::getNumVar() const
{
	return this->numvar;
}

