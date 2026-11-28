"""Exact SymPy stratified birth/extinction event and signed energy certificate.

Three charged species: electron charge -1, two positive ions +1.
Uses exact rational normalized-current algebra; no smooth D=0 derivative.
"""
import sympy as s
from itertools import product

def species(n,r,c,z,b,m,v,sign):
    assert n>=r>=0 and c>=0 and m>0 and v>0 and sign in (-1,1)
    if n==0:
        assert z==0
        velocity=s.Integer(0)
    else:
        velocity=sign*z/s.sqrt(m*v*n)
    survivor=n-r;new=survivor+c
    newvelocity=s.Integer(0) if new==0 else (survivor*velocity+c*b)/new
    znew=sign*s.sqrt(m*v*new)*newvelocity
    incoming=m*v*c*b*b/2
    removed=m*v*r*velocity*velocity/2
    mixing=s.Integer(0) if new==0 else m*v*survivor*c*(velocity-b)**2/(2*new)
    balance=s.simplify((znew*znew-z*z)/2-incoming+removed+mixing)
    assert balance==0
    if new==0:assert znew==0
    return znew,new

def fixture():
    # Electron conservation includes both positive ion channels at the event.
    populations=((0,0,0),(1,1,0),(1,0,1),(5,3,2),(2,2,0),(3,0,3))
    cases=0; births=deaths=0
    masses=(s.Rational(1,2),s.Integer(3),s.Integer(5))
    for e,ion1,ion2 in populations:
        assert e==ion1+ion2
        n=(e,ion1,ion2)
        for r1,r2,c1,c2 in product((0,1),repeat=4):
            if r1>ion1 or r2>ion2:continue
            r=(r1+r2,r1,r2); c=(c1+c2,c1,c2)
            if r[0]>e:continue
            assert -sum(c[:1])+c[1]+c[2]==0
            assert -(c[0]-r[0])+(c[1]-r[1])+(c[2]-r[2])==0
            for j in range(3):
                z=s.Integer(0) if n[j]==0 else s.Rational(j+2,7)
                b=s.Rational(j-1,5)
                _,new=species(n[j],r[j],c[j],z,b,masses[j],
                              s.Rational(7,3),-1 if j==0 else 1)
                births+=int(n[j]==0 and new>0)
                deaths+=int(n[j]>0 and new==0)
            cases+=1
    assert births>0 and deaths>0
    # Generator zero-mode obstruction, captured in companion checker.
    q,nu=s.symbols('q nu',positive=True)
    assert s.limit(s.sqrt(q*q)*nu,q,0)==0
    return dict(status='PASS',charge_neutral_events=cases,
                exact_species_energy_identities=cases*3,
                zero_to_positive_events=births,positive_to_zero_events=deaths,
                full_generator_jvp_admitted=False)
if __name__=='__main__':
    print(fixture())
