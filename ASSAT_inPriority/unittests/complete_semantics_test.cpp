#ifdef UNIT_TEST
#include "util_test.h"
using namespace std;

extern Encoding e;

bool test_complete_extensions(string file1, string file2)
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
//	int res = complete_extensions(&af, &sol);
//	if (res != 0)
//		throw gen_exception(res);
//
	set<set<string> > computed = set<set<string> >();
//	dMatrix_to_set_of_strings(&af, &sol, &computed);

	CompleteSemantics pref = CompleteSemantics(&af, e);
	pref.compute();
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

TEST(Complete, TestExceptionComplete1)
{
	ASSERT_THROW(test_complete_extensions("triciclo","triciclo.dl.complete"), gen_exception);
}

TEST(Complete, TestExceptionComplete2)
{
	ASSERT_THROW(test_complete_extensions("triciclo.dl","triciclo.d.complete"), gen_exception);
}

TEST(Complete, TestExceptionComplete3)
{
	ASSERT_THROW(test_complete_extensions("triciclo","triciclo.complete"), gen_exception);
}

TEST(Complete, CorrectSolutionComplete1)
{
	EXPECT_TRUE(test_complete_extensions("triciclo.dl","triciclo.dl.complete"));
}

TEST(Complete, CorrectSolutionComplete2)
{
	EXPECT_TRUE(test_complete_extensions("nixon.dl","nixon.dl.complete"));
}

TEST(Complete, CorrectSolutionComplete3)
{
	EXPECT_TRUE(test_complete_extensions("input0001.dl","input0001.dl.complete"));
}

TEST(Complete, IncorrectSolutionComplete1)
{
	EXPECT_TRUE(test_complete_extensions("triciclo.dl","triciclo.dl.wrong_complete") == false);
}

#endif
