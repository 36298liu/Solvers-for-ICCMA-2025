#ifdef UNIT_TEST
#include "util_test.h"

bool is_critical( gen_exception const& ex )
{	return ex.m_error_code < 0;}


bool are_equal_sets(set<set<string> > *s1, set<set<string> > *s2)
{
	return (*s1) == (*s2);
}

Encoding e = Encoding("111111");

#endif
