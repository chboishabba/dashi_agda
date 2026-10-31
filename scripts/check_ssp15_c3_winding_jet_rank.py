#!/usr/bin/env python3
"""Canonical SSP15 C3 Fourier-unwinding derivative-jet rank certificate.

For Z_v(theta)=sum v_p exp(i*p*theta), at theta0=2*pi/3,
i^(-k) Z_v^(k)(theta0) = A_k+B_k*zeta, where zeta^2+zeta+1=0.
The 2m x 15 integer matrix for (A_k,B_k), k<m, has exact rank
14 for m=9 and rank 15 for m=10: signed valuations recover from
first ten exact derivative jet values. No floats or prime infinitude.
"""
import sympy as s
P=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
def jet_matrix(m):
    def a(p): return 1 if p%3==0 else (-1 if p%3==2 else 0)
    def b(p): return 1 if p%3==1 else (-1 if p%3==2 else 0)
    return s.Matrix([[s.Integer(p)**k*a(p) for p in P] for k in range(m)]
                 + [[s.Integer(p)**k*b(p) for p in P] for k in range(m)])
def main():
    A9,A10=jet_matrix(9),jet_matrix(10)
    assert A9.rank()==14
    assert A10.rank()==15
    pivot_rows=A10.T.rref()[1]
    minor=A10[list(pivot_rows),:]
    determinant=minor.det(method="domain-ge")
    assert determinant!=0
    v=s.Matrix([0,2,1,-1,3,0,-2,0,1,4,0,1,0,-1,2])
    observed=A10*v
    recovered=minor.inv()*observed[list(pivot_rows),:]
    assert recovered==v
    # An explicit primitive integer kernel: two nonnegative valuation histories
    # with equal first nine complex jets, but different tenth jet.
    kernel=s.Matrix([-360448,0,1136200,0,-2624622,0,4499352,0,
                     -4686825,2499640,0,-807576,374946,-32890,2223])
    assert A9*kernel==s.zeros(18,1)
    assert A10*kernel!=s.zeros(20,1)
    positive=kernel.applyfunc(lambda x:max(x,0))
    negative=kernel.applyfunc(lambda x:max(-x,0))
    assert A9*positive==A9*negative
    assert A10*positive!=A10*negative
    # A single coordinate of the 10th jet separates the collision.
    assert (A10*kernel)[9]==-571323080827699200
    print("PASS explicit integral nine-jet collision and tenth-jet separation")
    print("primitive integer collision direction:",list(kernel))
    print("PASS canonical 15 SSP lanes; rank first 9 jets=14; rank first 10 jets=15")
    print("independent real/Eisenstein coordinates:",pivot_rows)
    print("nonzero 15x15 minor determinant:",determinant)
    print("PASS exact signed valuation recovery with rational linear algebra")
if __name__=="__main__":
    main()
