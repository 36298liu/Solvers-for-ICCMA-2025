#ifdef UNIT_TEST
using namespace std;
#include "util_test.h"

TEST(ArgumentOpTest, equal)
{
	AF test = AF();
	Argument a = Argument("a", 1, &test);
	Argument b = Argument("a", 1, &test);
	EXPECT_TRUE(a == b);
}

TEST(ArgumentOpTest, disequal)
{
	AF test = AF();
	Argument a = Argument("a", 1, &test);
	Argument b = Argument("b", 1, &test);
	EXPECT_TRUE(a != b);
}

TEST(SetArgumentsTest, equal_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	EXPECT_TRUE(a == b);
}

TEST(SetArgumentsTest, equal_2)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("a",1,NULL));
	b.add_Argument(new Argument("a",1,NULL));
	EXPECT_TRUE(a == b);
}

TEST(SetArgumentsTest, disequal_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("a",1,NULL));
	EXPECT_FALSE(a==b);
}

TEST(SetArgumentsTest, disequal_2)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	b.add_Argument(new Argument("a",1,NULL));
	EXPECT_FALSE(a==b);
}

TEST(SetArgumentsTest, exists_1)
{
	SetArguments a = SetArguments();
	Argument ar = Argument("a", 1, NULL);
	a.add_Argument(&ar);
	EXPECT_TRUE(a.exists(&ar));
}

TEST(SetArgumentsTest, exists_2)
{
	SetArguments a = SetArguments();
	Argument ar = Argument("a", 1, NULL);
	Argument ar2 = Argument("a", 2, NULL);
	a.add_Argument(&ar);
	EXPECT_TRUE(a.exists(&ar2));
}

TEST(SetArgumentsTest, nexists_1)
{
	SetArguments a = SetArguments();
	Argument ar2 = Argument("a", 2, NULL);
	EXPECT_FALSE(a.exists(&ar2));
}

TEST(SetArgumentsTest, nexists_2)
{
	SetArguments a = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	Argument ar2 = Argument("a", 2, NULL);
	EXPECT_FALSE(a.exists(&ar2));
}

TEST(SetArgumentsTest, remove_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	Argument ar2 = Argument("a", 2, NULL);
	a.add_Argument(&ar2);

	b.add_Argument(new Argument("c",1,NULL));
	a.remove(&ar2);
	EXPECT_TRUE(a == b);

}

TEST(SetArgumentsTest, subset_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	EXPECT_TRUE(b.is_subset(&a));
}

TEST(SetArgumentsTest, subseteq_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	EXPECT_TRUE(b.is_subset_equal(&a));
}

TEST(SetArgumentsTest, subset_2)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	EXPECT_FALSE(a.is_subset(&b));
}

TEST(SetArgumentsTest, subseteq_2)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	EXPECT_FALSE(a.is_subset_equal(&b));
}

TEST(SetArgumentsTest, subset_3)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("d",1,NULL));
	EXPECT_TRUE(b.is_subset(&a));
}

TEST(SetArgumentsTest, subseteq_3)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("d",1,NULL));
	EXPECT_TRUE(b.is_subset_equal(&a));
}

TEST(SetArgumentsTest, subset_4)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("d",1,NULL));
	EXPECT_FALSE(a.is_subset(&b));
}

TEST(SetArgumentsTest, subseteq_4)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("d",1,NULL));
	EXPECT_FALSE(a.is_subset_equal(&b));
}

TEST(SetArgumentsTest, subset_5)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("a",1,NULL));
	EXPECT_TRUE(b.is_subset(&a));
}

TEST(SetArgumentsTest, subseteq_5)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	a.add_Argument(new Argument("c",1,NULL));
	b.add_Argument(new Argument("c",1,NULL));
	a.add_Argument(new Argument("a",1,NULL));
	EXPECT_TRUE(b.is_subset_equal(&a));
}

TEST(SetArgumentsTest, subset_6)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	EXPECT_FALSE(a.is_subset(&b));
}

TEST(SetArgumentsTest, subseteq_6)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	EXPECT_TRUE(a.is_subset_equal(&b));
}

TEST(SetArgumentsTest, subset_7)
{
	SetArguments a = SetArguments();
	a.add_Argument(new Argument("a", 1, NULL));
	SetArguments b = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	EXPECT_FALSE(a.is_subset(&b));
}

TEST(SetArgumentsTest, subseteq_7)
{
	SetArguments a = SetArguments();
	a.add_Argument(new Argument("a", 1, NULL));
	SetArguments b = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	EXPECT_TRUE(a.is_subset_equal(&b));
}

TEST(SetArgumentsTest, intersect_1)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	SetArguments res = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	b.intersect(&a, &res);
	EXPECT_TRUE(res == a);
}

TEST(SetArgumentsTest, intersect_2)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	SetArguments res = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	a.intersect(&b, &res);
	EXPECT_TRUE(res == a);
}

TEST(SetArgumentsTest, intersect_3)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	SetArguments c = SetArguments();
	SetArguments res = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	b.add_Argument(new Argument("b", 2, NULL));
	b.add_Argument(new Argument("c", 3, NULL));
	a.add_Argument(new Argument("b", 2, NULL));
	a.add_Argument(new Argument("a", 1, NULL));
	c.add_Argument(new Argument("a", 1, NULL));
	c.add_Argument(new Argument("b", 2, NULL));

	b.intersect(&a, &res);
	EXPECT_TRUE(res == c);
}

TEST(SetArgumentsTest, intersect_4)
{
	SetArguments a = SetArguments();
	SetArguments b = SetArguments();
	SetArguments c = SetArguments();
	SetArguments res = SetArguments();
	b.add_Argument(new Argument("a", 1, NULL));
	b.add_Argument(new Argument("b", 2, NULL));
	b.add_Argument(new Argument("c", 3, NULL));
	a.add_Argument(new Argument("b", 2, NULL));
	a.add_Argument(new Argument("a", 1, NULL));
	c.add_Argument(new Argument("a", 1, NULL));
	c.add_Argument(new Argument("b", 2, NULL));

	a.intersect(&b, &res);
	EXPECT_TRUE(res == c);
}

#endif
