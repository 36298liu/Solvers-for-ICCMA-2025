#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"

extern Encoding e;

bool test_stable_extensions(string file1, string file2)
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
//	int res = stable_extensions(&af, &sol);
//	if (res != 0)
//		throw gen_exception(res);
//
	set<set<string> > computed = set<set<string> >();
//	dMatrix_to_set_of_strings(&af, &sol, &computed);

	StableSemantics pref = StableSemantics(&af, e);
	pref.compute();
	Semantics::iterator it;
	for (it = pref.begin(); it != pref.end(); it++)
	{
		set<string> asolutionmine = set<string>();
		SetArgumentsIterator argin;
		cout << (*(*it).inargs()) << endl;
		for (argin = (*it).inargs()->begin(); argin != (*it).inargs()->end(); argin++)
		{
			asolutionmine.insert((*argin)->getName());
		}
		computed.insert(asolutionmine);
	}

	return are_equal_sets(&test, &computed);
}


TEST(StableTest, TestExceptionStable1)
{
	ASSERT_THROW(test_stable_extensions("triciclo","triciclo.dl.stable"), gen_exception);
}

TEST(StableTest, TestExceptionStable2)
{
	ASSERT_THROW(test_stable_extensions("triciclo.dl","triciclo.d.stable"), gen_exception);
}

TEST(StableTest, TestExceptionStable3)
{
	ASSERT_THROW(test_stable_extensions("triciclo","triciclo.stable"), gen_exception);
}

TEST(StableTest, CorrectSolutionStable1)
{
	EXPECT_TRUE(test_stable_extensions("triciclo.dl","triciclo.dl.stable"));
}

TEST(StableTest, CorrectSolutionStable2)
{
	EXPECT_TRUE(test_stable_extensions("nixon.dl","nixon.dl.stable"));
}

TEST(StableTest, CorrectSolutionStable3)
{
	EXPECT_TRUE(test_stable_extensions("input0001.dl","input0001.dl.stable"));
}

TEST(StableTest, IncorrectSolutionStable1)
{
	EXPECT_TRUE(test_stable_extensions("triciclo.dl","triciclo.dl.wrong_stable") == false);
}

#endif
