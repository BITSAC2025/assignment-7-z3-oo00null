/**
 * verify.cpp
 * @author kisslune
 * Refactored for clarity and consistency (No Macros)
 */

#include "Z3Mgr.h"
#include <iostream>

using namespace z3;
using namespace SVF;

/*
 * A simple example
 * int main() {
 * int* p; int q; int* r; int x;
 * p = malloc();
 * q = 5;
 * *p = q;
 * x = *p;
 * assert(x==5);
 * }
 */
void Z3Tests::test0()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");

    // p = malloc();
    addToSolver(p == getMemObjAddress("malloc"));
    
    // q = 5;
    addToSolver(q == 5);
    
    // *p = q;
    storeValue(p, q);
    
    // x = *p;
    addToSolver(x == loadValue(p));

    // 逻辑保持：检查 x 是否可以等于 10 (基于原代码逻辑)
    addToSolver(x == getZ3Expr(10));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Simple integers
 * int main() {
 * int a; int b;
 * a = 0;
 * b = a + 1;
 * assert(b > 0);
 * }
 */
void Z3Tests::test1()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    // a = 0;
    addToSolver(a == getZ3Expr(0));

    // b = a + 1;
    addToSolver(b == a + 1);

    // assert(b > 0);
    addToSolver(b > getZ3Expr(0));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * One-level pointers
 * int main() {
 * int* p; int q; int b;
 * p = malloc;
 * *p = 0;
 * q = *p;
 * *p = 3;
 * b = *p + 1;
 * assert(b > 3);
 * }
 */
void Z3Tests::test2()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr b = getZ3Expr("b");

    // p = malloc;
    addToSolver(p == getMemObjAddress("malloc"));

    // *p = 0;
    storeValue(p, getZ3Expr(0));

    // q = *p;
    addToSolver(q == loadValue(p));

    // *p = 3;
    storeValue(p, getZ3Expr(3));

    // b = *p + 1;
    addToSolver(b == loadValue(p) + 1);

    // assert(b > 3);
    addToSolver(b > getZ3Expr(3));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Multiple-level pointers
 * int main() {
 * int** p; int* q; int* r; int x;
 * p = malloc1(..);
 * q = malloc2(..);
 * *p = q;
 * *q = 10;
 * r = *p;
 * x = *r;
 * assert(x==10);
 * }
 */
void Z3Tests::test3()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");

    // p = malloc1; q = malloc2;
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(q == getMemObjAddress("malloc2"));

    // *p = q;
    storeValue(p, q);

    // *q = 10;
    storeValue(q, getZ3Expr(10));

    // r = *p;
    addToSolver(r == loadValue(p));

    // x = *r;
    addToSolver(x == loadValue(r));

    // assert(x==10);
    addToSolver(x == getZ3Expr(10));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Array and pointers
 * int main() {
 * int* p; int* x; int* y; int a; int b;
 * p = malloc;
 * x = &p[0];
 * y = &p[1];
 * *x = 10;
 * *y = 11;
 * a = *x;
 * b = *y;
 * assert((a + b)>20);
 * }
 */
void Z3Tests::test4()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    addToSolver(p == getMemObjAddress("malloc"));

    // x = &p[0]; y = &p[1];
    addToSolver(x == getGepObjAddress(p, 0));
    addToSolver(y == getGepObjAddress(p, 1));

    // *x = 10; *y = 11;
    storeValue(x, getZ3Expr(10));
    storeValue(y, getZ3Expr(11));

    // a = *x; b = *y;
    addToSolver(a == loadValue(x));
    addToSolver(b == loadValue(y));

    // assert((a + b)>20);
    addToSolver((a + b) > getZ3Expr(20));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Branches
 * int main(int argv) {
 * int a; int b; int b1;
 * a = argv + 1;
 * b = 5;
 * if(a > 10) b = a;
 * b1 = b;
 * assert(b1 >= 5);
 * }
 */
void Z3Tests::test5()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr b1 = getZ3Expr("b1");
    expr argv = getZ3Expr("argv");

    addToSolver(a == argv + 1);

    // if (a > 10) b = a else b = 5
    addToSolver(b == ite(a > getZ3Expr(10), a, getZ3Expr(5)));

    addToSolver(b1 == b);
    
    // assert(b1 >= 5);
    addToSolver(b1 >= getZ3Expr(5));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Compare and pointers
 * int main() {
 * int *a = malloc1;
 * int *b = malloc2;
 * *a = 5;
 * *b = 10;
 * int *p;
 * if (*a < *b) { p = a; } else { p = b; }
 * assert(*p == 5);
 * }
 */
void Z3Tests::test6()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr p = getZ3Expr("p");

    addToSolver(a == getMemObjAddress("malloc1"));
    addToSolver(b == getMemObjAddress("malloc2"));

    // *a = 5; *b = 10;
    storeValue(a, getZ3Expr(5));
    storeValue(b, getZ3Expr(10));

    // if (*a < *b) p = a else p = b
    addToSolver(p == ite(loadValue(a) < loadValue(b), a, b));

    // assert(*p == 5);
    addToSolver(loadValue(p) == getZ3Expr(5));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * int main() {
 * int a = 1, b = 2, c = 3;
 * int d;
 * if (a > 0) { d = b + c; } else { d = b - c; }
 * assert(d == 5);
 * }
 */
void Z3Tests::test7()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");

    addToSolver(a == getZ3Expr(1));
    addToSolver(b == getZ3Expr(2));
    addToSolver(c == getZ3Expr(3));

    // d = (a > 0) ? (b + c) : (b - c)
    addToSolver(d == ite(a > getZ3Expr(0), b + c, b - c));

    // assert(d == 5);
    addToSolver(d == getZ3Expr(5));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * int main() {
 * int arr[2] = {0, 1};
 * int a = 10;
 * int *p;
 * if (a > 5) { p = &arr[0]; } else { p = &arr[1]; }
 * assert(*p == 0);
 * }
 */
void Z3Tests::test8()
{
    expr arr = getZ3Expr("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");

    // arr是数组的基地址
    addToSolver(arr == getMemObjAddress("arr"));

    // arr[0] = 0; arr[1] = 1;
    storeValue(getGepObjAddress(arr, 0), getZ3Expr(0));
    storeValue(getGepObjAddress(arr, 1), getZ3Expr(1));

    // a = 10;
    addToSolver(a == getZ3Expr(10));

    // if (a > 5) p = &arr[0] else p = &arr[1]
    addToSolver(p == ite(a > getZ3Expr(5),
                         getGepObjAddress(arr, 0),
                         getGepObjAddress(arr, 1)));

    // assert(*p == 0);
    addToSolver(loadValue(p) == getZ3Expr(0));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * Struct and pointers
 * struct A{ int f0; int* f1;};
 * int main() {
 * struct A* p;
 * int* x; int* q; int** r; int* y; int z;
 * p = malloc1;
 * x = malloc2;
 * *x = 5;
 * q = &(p->f0);
 * *q = 10;
 * r = &(p->f1);
 * *r = x;
 * y = *r;
 * z = *q + *y;
 * assert(z == 15);
 * }
 */
void Z3Tests::test9()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr y = getZ3Expr("y");
    expr z = getZ3Expr("z");

    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(x == getMemObjAddress("malloc2"));

    // *x = 5;
    storeValue(x, getZ3Expr(5));

    // q = &(p->f0);
    addToSolver(q == getGepObjAddress(p, 0));
    // *q = 10;
    storeValue(q, getZ3Expr(10));

    // r = &(p->f1);
    addToSolver(r == getGepObjAddress(p, 1));
    // *r = x;
    storeValue(r, x);

    // y = *r;
    addToSolver(y == loadValue(r));

    // z = *q + *y;
    addToSolver(z == loadValue(q) + loadValue(y));

    // assert(z == 15);
    addToSolver(z == getZ3Expr(15));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}

/*
 * int foo(int z) { k = z; return k; }
 * int main() {
 * int x; int y;
 * y = foo(2);
 * x = foo(3);
 * assert(x == 3 && y == 2);
 * }
 */
void Z3Tests::test10()
{
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");

    // y = foo(2); 返回 2
    addToSolver(y == getZ3Expr(2));

    // x = foo(3); 返回 3
    addToSolver(x == getZ3Expr(3));

    // assert(x == 3 && y == 2);
    addToSolver(x == getZ3Expr(3));
    addToSolver(y == getZ3Expr(2));

    printExprValues();
    std::cout << "Result: " << solver.check() << std::endl;
}


int main()
{
    Z3Tests tests;
    tests.test0();
    tests.resetSolver();
    tests.test1();
    tests.resetSolver();
    tests.test2();
    tests.resetSolver();
    tests.test3();
    tests.resetSolver();
    tests.test4();
    tests.resetSolver();
    tests.test5();
    tests.resetSolver();
    tests.test6();
    tests.resetSolver();
    tests.test7();
    tests.resetSolver();
    tests.test8();
    tests.resetSolver();
    tests.test9();
    tests.resetSolver();
    tests.test10();

    return 0;
}