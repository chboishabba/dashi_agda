"""Exact 12-channel Path13 pivot block controls, not nonflat source certification."""
import sympy as s
from random import Random

if __name__ == '__main__':
    if not __debug__: raise SystemExit('refusing optimized execution')
    N=13**4;I=s.eye(12);P0=I/N;G0=N*I
    assert G0*P0==I==P0*G0
    assert P0.det()==s.Rational(1,N)**12
    rng=Random(36913);count=2
    for _ in range(32):
        # Independent sparse noncommuting perturbation and free block.
        E=s.zeros(12);J=s.zeros(12)
        for i in range(11):
            E[i,i+1]=s.Rational(rng.randrange(-3,4),N)
            J[i+1,i]=s.Rational(rng.randrange(-3,4),N)
        P1=P0+E;G1=P1.inv()
        B0=s.Matrix(12,5,lambda i,j:s.Rational(rng.randrange(-3,4),N))
        B1=B0+J*B0;b=s.Matrix([rng.randrange(-3,4) for _ in range(5)])
        c0=-G0*B0*b;c1=-G1*B1*b
        assert P0*c0+B0*b==s.zeros(12,1);count+=1
        assert P1*c1+B1*b==s.zeros(12,1);count+=1
        assert c1-c0==-G1*(B1-B0)*b+G1*(P1-P0)*G0*B0*b;count+=1
        assert G0-G1==G1*(P1-P0)*G0;count+=1
    print(f'{count}/{count} Path13 block controls PASS')
