/**
 * @file 		Labelling.h
 * @author 		Federico Cerutti <federico.cerutti@acm.org>
 * @copyright	MIT
 */

#include <map>
#include <string>
using namespace std;

#include "Argument.h"
#include "SetArguments.h"

#ifndef LABELLING_H_
#define LABELLING_H_

typedef string Label;

class Labelling
{
	map<Argument *, Label> labelling;

	SetArguments in;
	SetArguments out;
	SetArguments undec;

public:

	const static Label lab_in;
	const static Label lab_out;
	const static Label lab_undec;
	Labelling();
	virtual ~Labelling();
	void add_label(Argument *, Label);
	bool exists_argument_labelling(Argument *);
	Label get_label(Argument *);
	SetArguments *inargs();
	SetArguments *outargs();
	SetArguments *undecargs();

	SetArguments getIn() const;
	SetArguments getOut() const;
	SetArguments getUndec() const;
	SetArguments extension() const;
	bool empty();
	void clone(Labelling *);
};

ostream& operator<<(ostream& out, const Labelling& r);

#endif /* LABELLING_H_ */
