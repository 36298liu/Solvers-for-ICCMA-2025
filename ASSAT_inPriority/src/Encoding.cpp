/**
 * @file 		Encoding.cpp
 * @class 		Encoding
 * @brief 		General class for a encoding for a SAT CNF
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include <Encoding.h>

bool Encoding::check()
{
	int sum = 0;
	for (int i = 0; i < NUMENCSPOS; i++)
	{
		sum += this->encodings[i];
	}

	if (sum < 3)
		return false;

	if (sum == 3)
	{
		if (
				(this->get_C_in_right() && this->get_C_out_right() && this->get_C_undec_right()) ||
				(this->get_C_in_left() && this->get_C_out_left() && this->get_C_undec_left())
			)
			return true;
		else
			return false;
	}

	if (sum == 4)
	{
		if (
				(this->get_C_undec_right() && this->get_C_undec_left() && this->get_C_in_right() && this->get_C_out_left()) ||
				(this->get_C_undec_right() && this->get_C_undec_left() && this->get_C_in_left() && this->get_C_out_right()) ||
				(this->get_C_out_right() && this->get_C_out_left() && this->get_C_in_right() && this->get_C_undec_left()) ||
				(this->get_C_out_right() && this->get_C_out_left() && this->get_C_in_left() && this->get_C_undec_right()) ||
				(this->get_C_in_right() && this->get_C_in_left() && this->get_C_out_right() && this->get_C_undec_left()) ||
				(this->get_C_in_right() && this->get_C_in_left() && this->get_C_out_left() && this->get_C_undec_right())
			)
			return false;
	}
	return true;
}


/**
 * @brief			Constructor for an Encoding
 * @param[in] i		Input string representing the desired encoding according to TAFA-13 post proceedings
 *						Pos 1 | Pos 2 | Pos 3 | Pos 4 | Pos 5 | Pos 6
 *						------|-------|-------|-------|-------|------
 * 						\f$C_{in}^{\rightarrow}\f$ | \f$C_{in}^{\leftarrow}\f$ | \f$C_{out}^{\rightarrow}\f$ | \f$C_{out}^{\leftarrow}\f$ | \f$C_{undec}^{\rightarrow}\f$ | \f$C_{undec}^{\leftarrow}\f$
 * 						e.g. "1 0 1 0 1 0" is equivalent to:
 * 						* \f$C_{in}^{\rightarrow}\f$, and
 * 						* \f$C_{out}^{\rightarrow}\f$, and
 * 						* \f$C_{undec}^{\rightarrow}\f$
 * 	@throws			StringLengthException
 * 	@throws			WeakEncoding
 */
Encoding::Encoding(string i)
{
	if (i.length() != NUMENCSPOS)
	{
		throw StringLengthException();
	}

	int j = 0;
	for (string::iterator it = i.begin(); it != i.end(); it++)
	{
		this->encodings[j++] = *(it) - '0';
	}
	if (!this->check())
	{
		throw WeakEnconding();
	}
}


/**
 * @return true if \f$C_{in}^{\rightarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_in_right() const
{
	return this->encodings[POS_C_IN_RIGHT];
}

/**
 * @return true if \f$C_{in}^{\leftarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_in_left() const
{
	return this->encodings[POS_C_IN_LEFT];
}

/**
 * @return true if \f$C_{out}^{\rightarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_out_right() const
{
	return this->encodings[POS_C_OUT_RIGHT];
}

/**
 * @return true if \f$C_{out}^{\leftarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_out_left() const
{
	return this->encodings[POS_C_OUT_LEFT];
}

/**
 * @return true if \f$C_{undec}^{\rightarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_undec_right() const
{
	return this->encodings[POS_C_UNDEC_RIGHT];
}

/**
 * @return true if \f$C_{out}^{\leftarrow}\f$ is selected, false otherwise
 */
bool Encoding::get_C_undec_left() const
{
	return this->encodings[POS_C_UNDEC_LEFT];
}

Encoding::~Encoding()
{

}

std::ostream& operator<<(std::ostream &out, const Encoding &e) {
  return out << e.get_C_in_right() << e.get_C_in_left() << e.get_C_out_right() << e.get_C_out_left() << e.get_C_undec_right() << e.get_C_undec_left();
}
