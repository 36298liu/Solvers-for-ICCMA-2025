#ifdef UNIT_TEST
#ifndef UTIL_TEST_H_
#define UTIL_TEST_H_

#include "gtest/gtest.h"
#include "argsemsat.h"
const string base_dir = "./unittests/input-tests/";

struct gen_exception
{
	explicit gen_exception(int ec = 0) :
			m_error_code(ec)
	{
	}

	int m_error_code;
};

bool is_critical(gen_exception const& ex);
bool are_equal_sets(set<set<string> > *s1, set<set<string> > *s2);

#endif /* UTIL_TEST_H_ */
#endif
