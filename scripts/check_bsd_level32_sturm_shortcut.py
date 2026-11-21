#!/usr/bin/env python3
"""Original E32 finite Sturm coefficient test; not an analytic modularity proof."""
import json
import sympy as sp

def direct_ap(p):
    points=1
    for x in range(p):
        value=(x*x*x-x)%p
        points+=sum(y*y%p==value for y in range(p))
    return p+1-points

def main():
    q=sp.symbols('q')
    index=sp.Integer(32)*(1+sp.Rational(1,2))
    bound=(2*index)//12
    assert index==48 and bound==8
    checks=2
    f=q
    for n in range(1,3):
        f=sp.expand(f*(1-q**(4*n))**2*(1-q**(8*n))**2)
    eta=[int(f.coeff(q,n)) for n in range(1,9)]
    assert eta==[1,0,0,0,-2,0,0,0];checks+=1
    ap={p:direct_ap(p) for p in (3,5,7)}
    assert ap=={3:0,5:-2,7:0};checks+=3
    # Bad additive p=2: local Euler polynomial=1, all even a_n=0.
    e=[1,0,ap[3],0,ap[5],0,ap[7],0]
    for a,b in zip(e,eta):
        assert a==b
        checks+=1
    assert len(e)==bound;checks+=1
    fake=[1]*8
    assert fake[0]==e[0] and fake[4]!=e[4];checks+=1
    print(json.dumps(dict(status='PASS',checks=checks,level=32,weight=2,
        index=int(index),sturm_bound=int(bound),
        original_E32_first_eight=e,eta_first_eight=eta,
        direct_prime_traces=ap,
        limitation='Sturm all-n implication requires two authentic same-character level-32 weight-2 modular forms; original E32 Mellin L-function and analytic modularity remain open'),indent=2,sort_keys=True))

if __name__=='__main__':main()
