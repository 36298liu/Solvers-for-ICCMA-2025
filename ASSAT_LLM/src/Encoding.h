/**
 * @file 		Encoding.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include <string>
#include <exception>
#include <iostream>
#include <array>
using namespace std;

#ifndef ENCODING_H_
#define ENCODING_H_

/**
 * @class StringLengthException
 * Exception raised if the string passed to
 * #Encoding:#Encoding is not 6 characters long
 */
class StringLengthException: public exception
{
	virtual const char* what() const throw ()
	{
		return "String Length Exception";
	}
};

/**
 * @class WeakEncoding
 * Exception raised if the string passed to
 * #Encoding:#Encoding is a weak encoding (i.e. it does not
 * codify enough constraints for determining a complete extensions,
 * cf. TAFA-13 post proceedings)
 */
class WeakEnconding: public exception
{
	virtual const char* what() const throw ()
	{
		return "Weak Encoding";
	}
};

#define NUMENCSPOS 			6

#define POS_C_IN_RIGHT 		0
#define POS_C_IN_LEFT  		1
#define POS_C_OUT_RIGHT 	2
#define POS_C_OUT_LEFT  	3
#define POS_C_UNDEC_RIGHT 	4
#define POS_C_UNDEC_LEFT  	5

class Encoding
{
private:
	friend std::ostream& operator<<(std::ostream&, const Encoding&);
	array<bool, NUMENCSPOS> encodings;
	bool check();
public:
	Encoding(string i);
	Encoding(){};
	virtual ~Encoding();
	bool get_C_in_right() const;
	bool get_C_in_left() const;
	bool get_C_out_right() const;
	bool get_C_out_left() const;
	bool get_C_undec_right() const;
	bool get_C_undec_left() const;
};

#endif /* ENCODING_H_ */
