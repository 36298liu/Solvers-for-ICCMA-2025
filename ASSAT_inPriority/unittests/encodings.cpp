#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"
#include "Encoding.h"
#include <string>

TEST(Encoding, conversion1)
{
	string s = "901299";
	Encoding e = Encoding(s);
	cerr << e << endl;
	EXPECT_TRUE(e.get_C_in_right() && !e.get_C_in_left() && e.get_C_out_right() && e.get_C_out_left() && e.get_C_undec_right() && e.get_C_undec_left());
}

TEST(Encoding, weak0)
{
	string s = "000000";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

TEST(Encoding, weak1)
{
	string s = "010000";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

TEST(Encoding, weak2)
{
	string s = "110000";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

TEST(Encoding, weak3)
{
	string s = "110100";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

TEST(Encoding, weak4a)
{
	string s = "110110";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

TEST(Encoding, weak4b)
{
	string s = "011011";
	ASSERT_ANY_THROW(Encoding e = Encoding(s));
}

#endif
