#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"

extern Encoding e;

bool test_preferred_extensions_df(string file1, string file2)
{
	satsolver = glucose;
	SatSolver = &glucose_lib;
	AF af = AF();
	if (af.readFile(base_dir + file1) == false)
		throw gen_exception( -1 );

	set<set<string> > test = set<set<string> >();
	if (!parse_solution_aspartix(&test, (base_dir + file2).c_str()))
		throw gen_exception( -2 );
//
//	dMatrix sol = dMatrix();
//
//	int res = preferred_extensions(&af, &sol);
//	if (res != 0)
//		throw gen_exception(res);
//
	set<set<string> > computed = set<set<string> >();
//	dMatrix_to_set_of_strings(&af, &sol, &computed);

	PreferredSemantics pref = PreferredSemantics(&af, e);
	pref.compute_depht_first();
	Semantics::iterator it;
	for (it = pref.begin(); it != pref.end(); it++)
	{
		set<string> asolutionmine = set<string>();
		SetArgumentsIterator argin;
		for (argin = (*it).inargs()->begin(); argin != (*it).inargs()->end(); argin++)
		{
			asolutionmine.insert((*argin)->getName());
		}
		computed.insert(asolutionmine);
	}

	return are_equal_sets(&test, &computed);
}


TEST(PreferredDF, TestExceptionPreferredDF1)
{
	ASSERT_THROW(test_preferred_extensions_df("triciclo","triciclo.dl.preferred"), gen_exception);
}

TEST(PreferredDF, TestExceptionPreferredDF2)
{
	ASSERT_THROW(test_preferred_extensions_df("triciclo.dl","triciclo.d.preferred"), gen_exception);
}

TEST(PreferredDF, TestExceptionPreferredDF3)
{
	ASSERT_THROW(test_preferred_extensions_df("triciclo","triciclo.preferred"), gen_exception);
}

TEST(PreferredDF, CorrectSolutionPreferredDF1)
{
	EXPECT_TRUE(test_preferred_extensions_df("triciclo.dl","triciclo.dl.preferred"));
}

TEST(PreferredDF, CorrectSolutionPreferredDF2)
{
	EXPECT_TRUE(test_preferred_extensions_df("nixon.dl","nixon.dl.preferred"));
}

TEST(PreferredDF, CorrectSolutionPreferredDF3)
{
	EXPECT_TRUE(test_preferred_extensions_df("input0001.dl","input0001.dl.preferred"));
}

TEST(PreferredDF, IncorrectSolutionPreferredDF1)
{
	EXPECT_TRUE(test_preferred_extensions_df("triciclo.dl","triciclo.dl.wrong_preferred") == false);
}

#endif
