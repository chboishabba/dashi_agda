#!/usr/bin/env python3
"""Original UNPROJECTED axial NS R236 source: all 18,513 output incidences.
WARNING: this old axial source has M parallel to output k and P_k M=0.
For nonzero Leray-transverse work use check_ns_transverse_large_bite_20261123.py.

Owner chain: NSTriadKNPhysicalTriadEnumeration, PhysicalOutputFiber,
NSTriadKNFixedOutputMixedCommutatorDampedTangentExact.mixedProductCell,
NSTriadKNMixedHelicityDampedProductTangentRound231Exact.mixedProduct,
R179.realHermitianCross, R236 CriticalRegionPairBlocks and Bony Round25.
Only exact finite initial Fourier geometry is checked; no PDE-time estimate,
native Agda kernel or universal sign claim is implied.
"""
from fractions import Fraction as Q
from collections import Counter, defaultdict
from itertools import product
from sympy import Matrix, I, Rational, simplify, symbols, Poly, discriminant, expand

CUT = 16
K = (16, 0, 0)

def shell(v):
    mag = max(map(abs, v))
    return 0 if mag <= 1 else (mag - 1).bit_length()

def region(p, q):
    jp, jq, jk = shell(p), shell(q), shell(K)
    if jp + 3 < jq:  # STRICT original Round25, not <=
        return 'FL' if 3 * jp <= 2 * jq else 'CC'
    if jq + 3 < jp:
        return 'FL' if 3 * jq <= 2 * jp else 'CC'
    if jk + 3 < max(jp, jq):
        return 'HH' if 5 * jk <= 4 * max(jp, jq) else 'CC'
    return 'CC'

def fibre():
    for x in range(-CUT, CUT + 1):
        qx = K[0] - x
        if not -CUT <= qx <= CUT:
            continue
        for y, z in product(range(-CUT, CUT + 1), repeat=2):
            p, q = (x, y, z), (qx, -y, -z)
            yield p, q, x*x + qx*qx + 2*y*y + 2*z*z, region(p, q)

def projector_contract():
    hplus, hminus = Matrix([0,1,I]), Matrix([0,1,-I])
    ex = Matrix([1,0,0])
    assert I * ex.cross(hplus) == hplus
    assert I * ex.cross(hminus) == -hminus
    assert hplus.cross(hminus) == Matrix([-2*I,0,0])
    for a,b in [(Rational(1), Rational(13,2)), (Rational(1), Rational(-10))]:
        v = a*hplus + b*hminus
        assert simplify((v+I*ex.cross(v))/2-a*hplus) == Matrix([0,0,0])
        assert simplify((v-I*ex.cross(v))/2-b*hminus) == Matrix([0,0,0])
        assert ex.dot(v) == 0
        assert simplify(I*(-ex).cross(v.conjugate())-(I*ex.cross(v)).conjugate()) == Matrix([0,0,0])

def evaluate(rows, b):
    # All original spectator incidences retained with work zero.
    active = {(1,15):b[15], (8,8):b[8], (15,1):b[1]}
    H = sum(b.values(),Q(0))
    n=Counter(); rate=defaultdict(int)
    work=defaultdict(lambda: Q(0)); weighted=defaultdict(lambda: Q(0))
    nonzero=[]
    for p,q,r,t in rows:
        n[t]+=1;rate[t]+=r
        scalar = active.get((p[0],q[0]),Q(0)) if p[1:]==(0,0) else Q(0)
        wi = 8*H*scalar   # A=-2i*b*e_x, M=-2i*H*e_x, w=2 Re<M,A>
        work[t]+=wi;weighted[t]+=r*wi
        if wi:nonzero.append((t,r,wi))
    keys=('FL','HH','CC')
    blocks={}
    for i,a in enumerate(keys):
        for c in keys[i:]:
            blocks[a,c]=(rate[a]*work[a]-n[a]*weighted[a] if a==c else
                rate[a]*work[c]+rate[c]*work[a]-n[c]*weighted[a]-n[a]*weighted[c])
    signed=sum(blocks.values(),Q(0))
    assert len(rows)==sum(n.values())==18513
    assert sum(work.values(),Q(0))==8*H*H
    assert signed==sum(rate.values())*sum(work.values(),Q(0))-len(rows)*sum(weighted.values(),Q(0))
    # Independent pair enumeration retaining all zero-work spectators.
    slow=defaultdict(lambda: Q(0))
    for a,ra,wa in nonzero:
        for p,q,r,t in rows:
            if p[1:]==(0,0) and (p[0],q[0]) in active:continue
            slow[tuple(sorted((a,t),key=keys.index))]-=(ra-r)*wa
    for i,(a,ra,wa) in enumerate(nonzero):
        for t,r,w in nonzero[i+1:]:
            slow[tuple(sorted((a,t),key=keys.index))]-=(ra-r)*(wa-w)
    assert all(blocks[k]==slow[k] for k in blocks)
    return signed,blocks,n,rate,4*H*H

def main():
    projector_contract()
    rows=list(fibre())
    assert len(rows)==17*33*33==18513
    assert sum(r for _,_,r,_ in rows)==9972336

    # All-finite-source *nonuniform* signed energy payment:
    # S=-2*N*Re<M,sum(r-mu) A>, and complex cross-product Lagrange
    # plus convolution Cauchy gives
    # |S|² <= (2N)² ||M||² sum(r-mu)² E_plus E_minus.
    N=len(rows);mu=Q(1616,3)
    variance=sum((Q(r)-mu)**2 for _,_,r,_ in rows)
    assert variance==1005066656
    t=symbols('t',real=True)
    eplus=12 # 3 positive modes + conjugate negative modes, ||h+||²=2
    eminus=4*(2*t**2+(3-2*t)**2)
    s=547392384-87085152*t
    certificate=expand((2*N)**2*36*variance*eplus*eminus-s*s)
    polynomial=Poly(certificate,t)
    assert polynomial.LC()>0 and discriminant(certificate,t)<0
    print('PASS full-source finite energy ceiling for all real t; rate variance',variance)

    assert Counter(t for _,_,_,t in rows)=={'CC':18477,'FL':36}
    tagged={(p[0],q[0]):t for p,q,_,t in rows
            if p[1:]==(0,0) and (p[0],q[0]) in {(1,15),(8,8),(15,1)}}
    assert tagged=={(1,15):'FL',(8,8):'CC',(15,1):'FL'}
    # Same original physical M=-6i*e_x, but opposite signed covariance.
    pos=evaluate(rows,{1:Q(1),8:Q(1),15:Q(1)})
    neg=evaluate(rows,{1:Q(13,2),8:Q(-10),15:Q(13,2)})
    assert pos[0]==460307232 and neg[0]==-18661104
    assert pos[4]==neg[4]==36 and pos[2:4]==neg[2:4]
    # Entire exact one-parameter family, b1=b15=t, b8=3-2t:
    # signed S(t)=547392384 - 87085152*t, root precisely t=44/7.
    t0=Q(44,7)
    assert 547392384 - 87085152*t0 == 0
    zero=evaluate(rows,{1:t0,8:3-2*t0,15:t0})
    assert zero[0]==0
    for label,received in [('positive',pos),('negative',neg),('zero',zero)]:
        print(label,'signed',received[0],'M_norm_sq',received[4],
              'six_blocks',dict(received[1]))
    print('PASS full physical fixed-output fibre, exact original helical projectors, '
          'reality, R236 strict routing, all spectators, independent signed blocks')
    print('SOURCE-NOGO: original rate geometry + fixed coherent M alone cannot give a signed payment')
    print('Leray caveat: this axial M is longitudinal, P_k M=0. Do not treat it as a nonzero projected-output R568 witness.')
    print('OPEN: true NS trajectory, source-specific positive estimates, cutoff-uniform sum, Agda kernel')

if __name__=='__main__':main()
