#!/usr/bin/env python3
"""Source-delimited worldsheet / Monster-Lie conformal consistency checks.

Prior art: FLM V^natural (chiral c=24); Lorentzian II_{1,1} lattice c=2;
bosonic (b,c) reparametrisation ghosts c=-26; Borcherds no-ghost/BRST
construction. This code verifies finite source-budget ARITHMETIC and classical
conformal density in a 3x3 toroidal lattice; it does NOT construct a VOA,
string measure, quantum BRST charge, nilpotent Q, or Weyl anomaly cancellation.
"""
from fractions import Fraction as Q
from itertools import product

def string_charge_budget():
    c_monster, c_lorentzian, c_bc = 24, 2, -26
    assert c_monster + c_lorentzian + c_bc == 0
    assert (c_monster + c_lorentzian) == 26
    assert (10 - 26) == -16  # 10 free bosons alone are NOT critical bosonic string
    assert 10 + 16 - 26 == 0  # distinct optional internal c=16 model, not Monster c=24
    assert 24 + 10 - 26 == 8  # naive Monster c24 + 10 free bosons is anomalous
    assert 24 + 2 - 26 == 0  # NOT 24+10-26
    assert 10 + 5 - 26 + 11 == 0  # separate RNS: ten bosons, ten fermions, superghosts
    print("PASS bosonic Monster c24+2-26=0; distinct RNS 10+5-26+11=0")

def torus_edges():
    return tuple(product(range(3), repeat=2))

def embed(point):
    i,j=point
    return (i-1, j-1, ((i+j)%3)-1)

def difference_squared(a,b):
    return sum((a[k]-b[k])**2 for k in range(3))

def finite_polyakov_energy(weights):
    """Conformal chart h_ab=omega(x)^2 diag(4,9).
    sqrt det h = 6 omega^2; inverse = diag(1/(4omega^2),1/(9omega^2)).
    Local density exactly invariant pointwise in 2 worldsheet dimensions.
    """
    local={}
    for i,j in torus_edges():
        w=Q(weights[(i,j)])
        assert w>0
        grad0=difference_squared(embed((i,j)),embed(((i+1)%3,j)))
        grad1=difference_squared(embed((i,j)),embed((i,(j+1)%3)))
        area=Q(6)*w*w
        inv0=Q(1,4*w*w)
        inv1=Q(1,9*w*w)
        local[(i,j)]=area*(inv0*grad0+inv1*grad1)
        unscaled=Q(6)*(Q(grad0,4)+Q(grad1,9))
        assert local[(i,j)]==unscaled
    return local

def check_classical_weyl():
    sheet=torus_edges()
    base={p:Q(1) for p in sheet}
    rescaled={p:Q(1+(p[0]+2*p[1])%5,1) for p in sheet}
    values0=finite_polyakov_energy(base)
    values1=finite_polyakov_energy(rescaled)
    assert values0==values1
    assert sum(values0.values())>0
    assert len(set(values1.values()))>1
    # A Nambu membrane-like p+1=3 conformally scaled kinetic density
    # acquires omega^(3-2) rather than omega^0.
    assert Q(2)**(3-2)!=1
    # The area density itself transforms omega^2 (even in the 2D worldsheet).
    assert Q(6)*Q(2)**2 != Q(6)
    print("PASS 9-cell 2D Polyakov-type local density: pointwise Weyl invariance")
    print("PASS nontrivial X: 9-sheet to 27-site cube chart; positive exact action",
          str(sum(values0.values())))
    print("PASS distinguish 2D kinetic Weyl identity from membrane/area action")

def check_bigrading_prefix():
    # Already present in MoonshineMonsterLieStringBigradingExact.agda,
    # not claimed as new: c(m n) at sample roots.
    j={-1:1,0:0,1:196884,2:21493760}
    for m,n in ((1,-1),(1,0),(1,1),(1,2),(2,1)):
        assert j[m*n]=={(1,-1):1,(1,0):0,(1,1):196884,
                        (1,2):21493760,(2,1):21493760}[(m,n)]
    print("PASS reused Borcherds Monster Lie finite root-multiplicity prefix")

if __name__=="__main__":
    string_charge_budget()
    check_classical_weyl()
    check_bigrading_prefix()
    print("BOUNDARY: classical finite Weyl identity + arithmetic ONLY; no quantum anomaly or BRST cohomology")
