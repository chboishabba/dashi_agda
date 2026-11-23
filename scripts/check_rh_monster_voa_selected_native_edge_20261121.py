#!/usr/bin/env python3
"""Exact selected native P3^3 edge / C27 label / oriented 13-axis regression.

Checks source arithmetic only, NOT Agda kernel / VOA-mode inhabitation.
"""
from itertools import product

def canonical(point):
    first = next(t for t in point if t != 0)
    return tuple(first*x for x in point)

def chart_charge(point):
    # Original finite balanced-digit numeric chart; negative trit is 2.
    return sum({-1:2,0:0,1:1}[x]*3**j for j,x in enumerate(point))

def main():
    origin=(0,0,0)
    points=list(product((-1,0,1),repeat=3))
    oriented=[p for p in points if p!=origin]
    axes={canonical(p) for p in oriented}
    assert len(points)==27 and len(oriented)==26 and len(axes)==13
    edges=[(p,q) for i,p in enumerate(points) for q in points[i+1:]
           if sum(abs(a-b) for a,b in zip(p,q))==1]
    assert len(edges)==54
    assert all(chart_charge(p)!=chart_charge(q) for p,q in edges)
    assert all(canonical(tuple(-x for x in p))==canonical(p) for p in oriented)
    x=(1,0,0);xy=(1,1,0)
    assert (x,xy) in edges
    assert chart_charge(x)==1 and chart_charge(xy)==4
    assert (chart_charge(x)+3)%27==chart_charge(xy)
    assert canonical(x)==x and canonical(xy)==xy
    # The four-cycle is in the projective quotient. A lift changes
    # sheet on ONE edge: 0,0,1,0. This is not a closed ordinary
    # four-edge walk in the unquotiented 27-site graph.
    assignments=list(product((0,1),repeat=4))
    failures=sum(not ((a^b)==0 and (b^c)==0 and
                      (c^d)==1 and (d^a)==0)
                 for a,b,c,d in assignments)
    assert failures==16
    print("PASS 54 native edges; 54 distinct endpoint C27 charges")
    print("PASS selected native +Y edge: 1+3=4 modulo 27")
    print("PASS 26 oriented sites ↔ 13 antipodal axes")
    print("PASS 16/16 projective four-cycle sign assignments obstructed")
    print("OPEN actual literal VOA mode-charge receipt and signed indexed six-face transport")

if __name__=="__main__":main()
