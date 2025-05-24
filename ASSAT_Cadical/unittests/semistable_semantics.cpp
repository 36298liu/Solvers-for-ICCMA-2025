#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"

extern Encoding e;

bool test_semistable_extensions(string file1, string file2)
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
//	int res = semistable_extensions(&af, &sol);
//	if (res != 0)
//		throw gen_exception(res);
//
	set<set<string> > computed = set<set<string> >();
//	dMatrix_to_set_of_strings(&af, &sol, &computed);

	SemistableSemantics pref = SemistableSemantics(&af, e);
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


TEST(SemistableTest, TestExceptionSemistable1)
{
	ASSERT_THROW(test_semistable_extensions("triciclo","triciclo.dl.semistable"), gen_exception);
}

TEST(SemistableTest, TestExceptionSemistable2)
{
	ASSERT_THROW(test_semistable_extensions("triciclo.dl","triciclo.d.semistable"), gen_exception);
}

TEST(SemistableTest, TestExceptionSemistable3)
{
	ASSERT_THROW(test_semistable_extensions("triciclo","triciclo.semistable"), gen_exception);
}

TEST(SemistableTest, CorrectSolutionSemistable1)
{
	EXPECT_TRUE(test_semistable_extensions("triciclo.dl","triciclo.dl.semistable"));
}

TEST(SemistableTest, CorrectSolutionSemistable2)
{
	EXPECT_TRUE(test_semistable_extensions("nixon.dl","nixon.dl.semistable"));
}

TEST(SemistableTest, CorrectSolutionSemistable3)
{
	EXPECT_TRUE(test_semistable_extensions("input0001.dl","input0001.dl.semistable"));
}

TEST(SemistableTest, IncorrectSolutionSemistable1)
{
	EXPECT_TRUE(test_semistable_extensions("triciclo.dl","triciclo.dl.wrong_semistable") == false);
}

#endif
