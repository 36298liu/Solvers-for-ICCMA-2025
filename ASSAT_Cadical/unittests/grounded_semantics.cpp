#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"

extern Encoding e;

bool test_grounded_extensions(string file1, string file2)
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
//	int res = grounded_extensions(&af, &sol);
//	if (res != 0)
//		throw gen_exception(res);
//
	set<set<string> > computed = set<set<string> >();
//	dMatrix_to_set_of_strings(&af, &sol, &computed);

	GroundedSemantics pref = GroundedSemantics(&af, e);
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


TEST(GroundedTest, TestExceptionGrounded1)
{
	ASSERT_THROW(test_grounded_extensions("triciclo","triciclo.dl.grounded"), gen_exception);
}

TEST(GroundedTest, TestExceptionGrounded2)
{
	ASSERT_THROW(test_grounded_extensions("triciclo.dl","triciclo.d.grounded"), gen_exception);
}

TEST(GroundedTest, TestExceptionGrounded3)
{
	ASSERT_THROW(test_grounded_extensions("triciclo","triciclo.grounded"), gen_exception);
}

TEST(GroundedTest, CorrectSolutionGrounded1)
{
	EXPECT_TRUE(test_grounded_extensions("triciclo.dl","triciclo.dl.grounded"));
}

TEST(GroundedTest, CorrectSolutionGrounded2)
{
	EXPECT_TRUE(test_grounded_extensions("nixon.dl","nixon.dl.grounded"));
}

TEST(GroundedTest, CorrectSolutionGrounded3)
{
	EXPECT_TRUE(test_grounded_extensions("input0001.dl","input0001.dl.grounded"));
}

TEST(GroundedTest, IncorrectSolutionGrounded1)
{
	EXPECT_TRUE(test_grounded_extensions("triciclo.dl","triciclo.dl.wrong_grounded") == false);
}

#endif
