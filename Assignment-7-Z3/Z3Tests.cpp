/**
 * verify.cpp
 * @author kisslune
 */

#include "Z3Mgr.h"

using namespace z3;
using namespace SVF;

// ... (test0 is already provided in your snippet) ...

/*
// Simple integers
    int main() {
        int a;
        int b;
        a = 0;
        b = a + 1;
        assert(b > 0);
    }
*/
void Z3Tests::test1()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    // a = 0;
    addToSolver(a == 0);
    // b = a + 1;
    addToSolver(b == a + 1);
    
    // assert(b > 0);
    addToSolver(b > 0);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
  // One-level pointers
    int main() {
        int* p;
        int q;
        int b;
        p = malloc;
        *p = 0;
        q = *p;
        *p = 3;
        b = *p + 1;
        assert(b > 3);
    }
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
    addToSolver(b > 3);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Mutiple-level pointers
    int main() {
        int** p;
        int* q;
        int* r;
        int x;

        p = malloc1(..);
        q = malloc2(..);
        *p = q;
        *q = 10;
        r = *p;
        x = *r;
        assert(x==10);
    }
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
    addToSolver(x == 10);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
   // Array and pointers
    int main() {
        int* p;
        int* x;
        int* y;
        int a;
        int b;
        p = malloc;
        x = &p[0];
        y = &p[1]
        *x = 10;
        *y = 11;
        a = *x;
        b = *y;
        assert((a + b)>20);
    }
*/
void Z3Tests::test4()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    // p = malloc;
    addToSolver(p == getMemObjAddress("malloc"));

    // x = &p[0]; (Base address)
    addToSolver(x == p);

    // y = &p[1]; (Base + 1)
    addToSolver(y == p + 1);

    // *x = 10;
    storeValue(x, getZ3Expr(10));

    // *y = 11;
    storeValue(y, getZ3Expr(11));

    // a = *x;
    addToSolver(a == loadValue(x));

    // b = *y;
    addToSolver(b == loadValue(y));

    // assert((a + b)>20);
    addToSolver((a + b) > 20);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Branches
    int main(int argv) {
        int a;
        int b;
        int b1;
        a = argv + 1;
        b = 5;
        if(a > 10)
            b = a;
        b1 = b;
        assert(b1 >= 5);
    }
*/
void Z3Tests::test5()
{
    expr argv = getZ3Expr("argv");
    expr a = getZ3Expr("a");
    expr b1 = getZ3Expr("b1");

    // a = argv + 1;
    addToSolver(a == argv + 1);

    // Logic for b:
    // path1: b = 5
    // path2: b = a (if a > 10)
    // We use ITE (If-Then-Else) to merge the values (Phi node)
    expr cond = (a > 10);
    expr b_val = ite(cond, a, getZ3Expr(5));

    // b1 = b;
    addToSolver(b1 == b_val);

    // assert(b1 >= 5);
    addToSolver(b1 >= 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
// Compare and pointers
int main() {
   int *a = malloc1;
   int *b = malloc2;
   *a = 5;
   *b = 10;
   int *p;
   if (*a < *b) {
       p = a;
   } else {
       p = b;
   }
   assert(*p == 5);
}
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

    // if (*a < *b)
    expr valA = loadValue(a);
    expr valB = loadValue(b);
    expr cond = (valA < valB);

    // Merge logic for p: if true p=a, else p=b
    expr p_val = ite(cond, a, b);
    addToSolver(p == p_val);

    // assert(*p == 5);
    addToSolver(loadValue(p) == 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
    int a = 1, b = 2, c = 3;
    int d;
  if (a > 0) {
    d = b + c;
  }
  else {
    d = b - c;
  }
  assert(d == 5);
 }
 */
void Z3Tests::test7()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");

    // Init values
    addToSolver(a == 1);
    addToSolver(b == 2);
    addToSolver(c == 3);

    // if (a > 0)
    expr cond = (a > 0);
    
    // d values based on branch
    expr d_true = b + c;
    expr d_false = b - c;
    
    // Merge
    addToSolver(d == ite(cond, d_true, d_false));

    // assert(d == 5);
    addToSolver(d == 5);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
    int arr[2] = {0, 1};
    int a = 10;
    int *p;
    if (a > 5) {
        p = &arr[0];
    }
    else {
        p = &arr[1];
    }
    assert(*p == 0);
 }
 */
void Z3Tests::test8()
{
    expr arr = getMemObjAddress("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");

    // Initialize array: arr[0]=0, arr[1]=1
    // arr is the base address (index 0)
    storeValue(arr, getZ3Expr(0));
    // arr + 1 is index 1
    storeValue(arr + 1, getZ3Expr(1));

    addToSolver(a == 10);

    // if (a > 5)
    expr cond = (a > 5);

    // p = &arr[0] vs p = &arr[1]
    expr p_val = ite(cond, arr, arr + 1);
    
    addToSolver(p == p_val);

    // assert(*p == 0);
    addToSolver(loadValue(p) == 0);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
    // Struct and pointers
    struct A{ int f0; int* f1;};
    int main() {
       struct A* p;
       int* x;
       int* q;
       int** r;
       int* y;
       int z;

       p = malloc1;
       x = malloc2;
       *x = 5;
       q = &(p->f0);
       *q = 10;
       r = &(p->f1);
       *r = x;
       y = *r;
       z = *q + *y;
       assert(z == 15);
    }
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

    // q = &(p->f0); -> Offset 0
    addToSolver(q == p);

    // *q = 10;
    storeValue(q, getZ3Expr(10));

    // r = &(p->f1); -> Offset 1 (Assuming 1 field size)
    addToSolver(r == p + 1);

    // *r = x;
    storeValue(r, x);

    // y = *r;
    addToSolver(y == loadValue(r));

    // z = *q + *y; 
    // Note: y is a pointer (from x), so we dereference y. 
    // *q is an int.
    addToSolver(z == loadValue(q) + loadValue(y));

    // assert(z == 15);
    addToSolver(z == 15);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

/*
int foo(int z) {
    k = z;
    return k;
}
int main() {
  int x;
  int y;
  y = foo(2);
  x = foo(3);
  assert(x == 3 && y == 2);
}
*/
void Z3Tests::test10()
{
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    
    // Since we don't have inter-procedural analysis infrastructure here,
    // we inline the logic of the function calls.
    
    // y = foo(2) -> returns 2
    addToSolver(y == 2);
    
    // x = foo(3) -> returns 3
    addToSolver(x == 3);
    
    // assert(x == 3 && y == 2);
    addToSolver(x == 3 && y == 2);

    printExprValues();
    std::cout << solver.check() << std::endl;
}

// ... main function is provided in your snippet ...


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