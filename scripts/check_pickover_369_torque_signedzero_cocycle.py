#!/usr/bin/env python3
"""Exact 3/9/27 torqued signed-circle cocycle and oriented-zero regression.

DASHI owners: TorqueTrialectic369Exact; SignedZeroTernaryOrientationExact;
OrientedZeroJetTransitionExact; PhaseQuotientNonaryGroupSeparationExact;
ConsumerIndexedResidualRefinementExact.  Ordinary rational arithmetic.
No claim about sin(99^(9999!)) or a real->3-adic analytic equivalence.
"""
from fractions import Fraction
from itertools import product

def circle(x):
    return x % 1

def sine_sign(x):
    r=circle(x)
    if r in (0, Fraction(1,2)): return 0
    return +1 if r<Fraction(1,2) else -1

def prefix_tail(x,depth):
    y=circle(x)*3**depth
    a=y.numerator//y.denominator
    return a,y-a

def assemble(a,r,depth):
    assert 0<=a<3**depth and 0<=r<1
    return (a+r)/3**depth

def digits3(a,depth):
    v=[0]*depth
    for i in range(depth-1,-1,-1):
        v[i]=a%3
        a//=3
    assert a==0
    return tuple(v)

def step99_from_grid(a,r):
    assert 0<=a<9 and 0<=r<1
    # 99*(a+r)/9=11*a+11*r
    return circle(11*r)

def step99_from_cube(a,r):
    grid,third=divmod(a,3)
    assert 0<=grid<9 and 0<=third<3 and 0<=r<1
    # 99*(a+r)/27 =11*grid+11*(third+r)/3
    return circle(Fraction(11,3)*(third+r))

def check_grid_cube():
    for denominator in (27,54,97,300,997):
        for numerator in range(denominator):
            x=Fraction(numerator,denominator)
            grid,r=prefix_tail(x,2)
            cube,t=prefix_tail(x,3)
            assert assemble(grid,r,2)==x
            assert assemble(cube,t,3)==x
            assert cube//3==grid
            assert digits3(cube,3)[:2]==digits3(grid,2)
            assert step99_from_grid(grid,r)==circle(99*x)
            assert step99_from_cube(cube,t)==circle(99*x)
    print('PASS exact 3x3 grid -> 3x3x3 cube, factor 99=9*11 tail transport')

def check_central_branch():
    for depth in range(1,13):
        centre=(3**depth-1)//2
        assert 2*centre+1==3**depth
        assert digits3(centre,depth)==(1,)*depth
        # Real: 0.111... in base 3 converges upward to +1/2.
        assert Fraction(1,2)-Fraction(centre,3**depth)==Fraction(1,2*3**depth)
        # 3-adic: centre+1/2=3**depth/2, valuation exactly depth.
        for r in (Fraction(1,7),Fraction(2,5),Fraction(1,2),
                  Fraction(3,4),Fraction(6,7)):
            x=assemble(centre,r,depth)
            assert x-Fraction(1,2)==(r-Fraction(1,2))/3**depth
            assert sine_sign(x)==sine_sign(r)
    print('PASS central all-ones branch: simultaneous real +1/2 and 3-adic -1/2 convergence')

def germ(boundary,direction):
    # Signed-zero sites: x=0 and x=1/2; approach from +/- phase side.
    assert boundary in (0,Fraction(1,2)) and direction in (-1,+1)
    eps=Fraction(1,100000)
    x=circle(boundary+direction*eps)
    assert circle(99*boundary)==boundary # odd 99 fixes both sites
    assert circle(99*x)==circle(boundary+direction*99*eps)
    assert sine_sign(x)==sine_sign(99*x)
    return sine_sign(x)

def check_germs():
    assert germ(0,-1)==-1 and germ(0,+1)==+1
    assert germ(Fraction(1,2),-1)==+1
    assert germ(Fraction(1,2),+1)==-1
    print('PASS four directed signed-zero germs; positive ×99 fixes each local germ')

def itinerary_witness(word):
    # Explicit inverse branches in the two sign chambers:
    # (1+y)/99 in (0,1/2), (60+y)/99 in (1/2,1).
    y=Fraction(1,4)
    for s in reversed(word):
        y=((1 if s==+1 else 60)+y)/99
    return y

def check_global_finite_quotient(depth=9):
    for word in product((+1,-1),repeat=depth):
        x=itinerary_witness(word)
        assert all(sine_sign(99**i*x)==s for i,s in enumerate(word))
    # Every signed length-d itinerary occurs: an exactly faithful
    # deterministic finite-state quotient needs >=2**d states to
    # represent all real-circle phases through depth d.
    print('PASS',2**depth,'distinct reachable signed itineraries; all-phase finite quotient no-go')


def first_noncentral_certificate(x,maxdepth=80):
    """First trit not equal to the central 1 decides the half-circle sign.
    Zero phase must be checked separately; 1/2 is 0.111... base 3.
    """
    r=circle(x)
    if r==0:return 0,0
    for depth in range(1,maxdepth+1):
        y=3*r
        digit=y.numerator//y.denominator
        assert 0<=digit<=2
        r=y-digit
        if digit!=1:
            return (1 if digit==0 else -1),depth
    return None,maxdepth

def check_first_noncentral():
    for denominator in range(2,250):
        for numerator in range(1,denominator):
            x=Fraction(numerator,denominator)
            s,depth=first_noncentral_certificate(x)
            if x==Fraction(1,2):
                assert s is None
            else:
                assert s==sine_sign(x)
    for depth in range(1,13):
        centre=(3**depth-1)//2
        for r in (Fraction(1,7),Fraction(6,7)):
            x=assemble(centre,r,depth)
            s,k=first_noncentral_certificate(x)
            assert s==sine_sign(x)
            assert k>depth
    print('PASS first noncentral ternary digit gives exact signed-phase certificate')

def main():
    check_grid_cube()
    check_central_branch()
    check_germs()
    check_global_finite_quotient()
    check_first_noncentral()
    print('OPEN source-specific alpha=1/(2*pi) signed cocycle, cheap factorial jump, final sine sign')

if __name__=='__main__':main()
