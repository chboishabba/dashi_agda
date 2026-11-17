#!/usr/bin/env python3
"""Independent exact symbolic check for Bishop SU2 matrix algebra.
Not a substitute for pinned Agda kernel acceptance.
"""
import sympy as sp
a,b,c,d=sp.symbols("q0 q1 q2 q3", real=True)
U=sp.Matrix([[a+sp.I*d,c+sp.I*b],[-c+sp.I*b,a-sp.I*d]])
norm=a*a+b*b+c*c+d*d
tests=0
def check(x,y,name):
    global tests
    delta=sp.expand(x-y)
    if delta!=0:
        raise AssertionError((name,delta))
    tests+=1
check(U.trace(),2*a,"raw trace")
check(U.det(),norm,"determinant norm")
gram=U.conjugate().T*U
for i in range(2):
    for j in range(2):
        check(sp.re(gram[i,j]),norm if i==j else 0,
              f"Gram real {i},{j}")
        check(sp.im(gram[i,j]),0,f"Gram imaginary {i},{j}")
# All 16 entries in U*U† and U†*U, tested separately.
for gram in (U.conjugate().T*U,U*U.conjugate().T):
    for i in range(2):
        for j in range(2):
            check(gram[i,j],norm if i==j else 0,
                  f"two-sided unitarity {i},{j}")
print(f"YM_REAL_BISHOP_MATRIX_SYMBOLIC_PASS={tests}")
