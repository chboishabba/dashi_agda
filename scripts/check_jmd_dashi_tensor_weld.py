"""Exact character-level tensor and obstruction tests; no Monster embedding claim."""
from itertools import product
import sympy as s

def check():
    T=s.Matrix([[1,1,2],[1,-1,0],[1,1,-1]])
    # Shared C3 remainder: one fixed point plus 1215 regular orbits.
    K=s.Matrix([1216,1215,1215]); assert sum(K)==3646
    def convolution(a,b):
        return s.Matrix([sum(a[i]*b[(j-i)%3] for i in range(3)) for j in range(3)])
    B=s.Matrix([54,0,0]); C=s.Matrix([18,18,18])
    assert convolution(B,K)==s.Matrix([65664,65610,65610])
    assert convolution(C,K)==s.Matrix([65628]*3)
    # Explicit product bijections of finite C3 sets, orbit counts.
    assert 54*1215==65610 and 18*3646==65628
    # Actual S3-restricted character, conditional on sourced 2A/3C labels.
    target=s.Matrix([196884,4372,0])
    R=s.Matrix([10,8,18]); Q=s.Matrix([2186,0,730])
    r=T*R; q=T*Q
    assert r==s.Matrix([54,2,0]) and q==s.Matrix([3646,2186,1456])
    assert r.multiply_elementwise(q)==target
    assert T.inv()*target==s.Matrix([35000,30628,65628])
    # Enumerate all character factorisations with these ordered dimensions.
    # At dim 3646 the rotation trace is 1 mod 3, thus R has trace 0.
    sols=[]
    for a in range(19):
        b=18-a; t=a-b
        if t==0 or 4372%t: continue
        u=4372//t
        for c in range(1824):
            rem=3646-2*c
            if (rem+u)%2: continue
            m=(rem+u)//2; n=(rem-u)//2
            if min(m,n)<0: continue
            v=s.Matrix([m,n,c]); rr=s.Matrix([a,b,18])
            assert (T*rr).multiply_elementwise(T*v)==target
            sols.append((a,b,18,m,n,c))
    assert (10,8,18,2186,0,730) in sols
    assert all(abs(a-b)==2 for a,b,*_ in sols)
    assert len(sols)==1462  # simultaneous sign twist gives the other half
    # Original free sixfold factor has zero reflection trace, even tensored
    # with an arbitrary representation (diagonal action).
    assert (T*s.Matrix([9,9,18]))[1]==0
    assert s.factorint(196884)=={2:2,3:3,1823:1}
    print('PASS: C3 shared tensor, S3 tensor, 1462 exhaustive ordered factorizations, free-sixfold obstruction')
if __name__=='__main__': check()
