/**
 * @file 		Labelling.cpp
 * @class 		Labelling
 * @brief 		Class representing a single labelling assignment
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */


#include "Labelling.h"

/**
 * @var Label Labelling::lab_in
 * @brief Label representing an `in` argument
 */
const Label Labelling::lab_in = "in";

/**
 * @var Label Labelling::lab_out
 * @brief Label representing an `out` argument
 */
const Label Labelling::lab_out = "out";

/**
 * @var Label Labelling::lab_undec
 * @brief Label representing an `undec` argument
 */
const Label Labelling::lab_undec = "undec";

/**
 * @brief	Constructor
 */
Labelling::Labelling()
{
	this->labelling = map<Argument *, Label>();
	this->in = SetArguments();
	this->out = SetArguments();
	this->undec = SetArguments();
}

/**
 * @brief	Add a new label to this set of labelling
 * @param[in] arg	The argument to which this labelling applies
 * @param[in] l		The label. Valid values for are:
 * 					 * Labelling::lab_in
 * 					 * Labelling::lab_out
 * 					 * Labelling::lab_undec
 */
void Labelling::add_label(Argument * arg, Label l)
{
	this->labelling.insert(pair<Argument *, Label>(arg, l));
	if (l.compare(Labelling::lab_in) == 0)
		this->in.add_Argument(arg);
	else if (l.compare(Labelling::lab_out) == 0)
		this->out.add_Argument(arg);
	else if (l.compare(Labelling::lab_undec) == 0)
		this->undec.add_Argument(arg);
}

/**
 * @brief	Check whether an argument is in this labelling or not
 * @param[in] arg A pointer to an Argument
 * @retval bool
 */
bool Labelling::exists_argument_labelling(Argument *arg)
{
	return (this->labelling.find(arg) != this->labelling.end());
}

/**
 * @brief Returns the label of a given argument
 * @param[in] arg	A pointer to an argument
 * @retval Label
 */
Label Labelling::get_label(Argument *arg)
{
	return this->labelling.at(arg);
}

/**
 * @brief Returns the set of arguments labelled as `in`
 * @retval SetArguments *
 */
SetArguments *Labelling::inargs()
{
	return &(this->in);
}

/**
 * @brief Returns the set of arguments labelled as `out`
 * @retval SetArguments *
 */
SetArguments *Labelling::outargs()
{
	return &(this->out);
}

/**
 * @brief Returns the set of arguments labelled as `undec`
 * @retval SetArguments *
 */
SetArguments *Labelling::undecargs()
{
	return &(this->undec);
}

/**
 * @brief Check whether or not this labelling is empty
 * @retval bool
 */
bool Labelling::empty()
{
	return this->labelling.empty() && this->in.empty() && this->out.empty() && this->undec.empty();
}

/**
 * @brief Clone this labelling into a new one
 * @param[out] other A pointer to a Labelling which will be the clone of this one
 * @retval void
 */
void Labelling::clone(Labelling *other)
{
	(*other) = Labelling();
	map<Argument *, Label>::iterator it;
	for (it = this->labelling.begin(); it != this->labelling.end(); it++)
	{
		other->add_label((*it).first, (*it).second);
	}
}

Labelling::~Labelling()
{
	// TODO Auto-generated destructor stub
}

SetArguments Labelling::getIn() const
{
	return this->in;
}
SetArguments Labelling::getOut() const
{
	return this->out;
}
SetArguments Labelling::getUndec() const
{
	return this->undec;
}

SetArguments Labelling::extension() const
{
	return this->in;
}

ostream& operator<<(ostream& out, const Labelling& r)
{
	out << r.extension();
	return out;
}
