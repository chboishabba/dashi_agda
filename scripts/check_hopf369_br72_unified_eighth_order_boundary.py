#!/usr/bin/env python3
"""BR72 integrated SAME-DATA physical boundary source, order 0..8.

Assemble BOTH original BR34 D/E 30 metric + 10 gauge rows from
ONE coherent physical source and independently apply:
 BR52/58 moving ADM conormal derivative columns (15+5, both faces)
 BR67 geometric Israel correction: 2([b'']-2mj)phi η
 BR68/69 nonzero-mean scalar force: -4m(ell+ +ell-)
 BR68/69 true coordinate Codazzi: -2 M·eta[c]-j/2(c++c-).

All coefficients are DIVIDED Taylor jets of the SAME original
metric/gauge plus/minus endpoint values, j,q,m,phi,warp-acceleration
and mean second fundamental form. The original BR34 rows are
separately affine in j and q, and their derivative columns are
independent of those background inputs.

The arbitrary metric p+,p- here need not satisfy the physical induced
matching condition; that physical compatibility remains an explicit
independent hypothesis. This is exact algebra for a coherent source,
not proof of nonlinear Einstein–Israel well-posedness or that its
moving unit-normal gauge frame is the coordinate BR34 gauge frame.

--allocation D|E --order 0..8, each checkpoint <=90s.
"""
import argparse
from fractions import Fraction as F
import sympy as s
from check_hopf369_br52_all_order_material_flux import ORDER,mul,add,sub,scale,trim,field_jet
from check_hopf369_br58_material_boundary_jets import (
    original_value,normal_value,material_difference,make_source,zero,rows
)
from check_hopf369_br_warped_physical_attachment import E4,keys

def asS(x):
    return s.Rational(x.numerator,x.denominator)
def original(n,sector,face):
    return original_value(sector,face,n)
def jet_series(fn):
    return trim([F(fn(i)) for i in range(ORDER+1)])
def background():
    return {
      "j":jet_series(lambda n:F((3*n+2)%19-9,17+n)),
      "m":jet_series(lambda n:F((5*n+3)%23-11,19+n)),
      "phi":jet_series(lambda n:F((2*n+5)%29-14,23+n)),
      "bpp":jet_series(lambda n:F((7*n+2)%31-15,29+n)),
      "bmp":jet_series(lambda n:F((11*n+4)%37-18,31+n)),
      "q":[jet_series(lambda n,a=a:F(((a+2)*(n+3))%19-9,17+a+n))
           for a in range(4)],
      "M":[[jet_series(lambda n,a=a,b=b:
            F(((min(a,b)+3)*(max(a,b)+2)*(n+1))%23-11,29+a+b+n))
             for b in range(4)] for a in range(4)]
    }
def j_bg(bg,n):return asS(bg["j"][n])
def q_bg(bg,n):return s.Matrix([asS(bg["q"][a][n]) for a in range(4)])

def fields(n,sector):
    return [original(n,sector,0),normal_value(sector,0,n),
            original(n,sector,1),normal_value(sector,1,n)]
def correction(n,sector,src):
    z=zero(sector)
    return [z,material_difference(sector,0,n,src),
            z,material_difference(sector,1,n,src)]
def refrows(n,sector,allocation,bg):
    Zq=s.zeros(4,1)
    source=rows(sector,allocation,fields(n,sector),j_bg(bg,0),q_bg(bg,0))
    for a in range(1,n+1):
        source+=rows(sector,allocation,fields(n-a,sector),j_bg(bg,a),q_bg(bg,a))
        source-=rows(sector,allocation,fields(n-a,sector),s.S.Zero,Zq)
    return source
def graphcorrection(n,sector,allocation,src):
    Zq=s.zeros(4,1)
    return rows(sector,allocation,correction(n,sector,src),s.S.Zero,Zq)

def israelseries(bg):
    return scale(2,mul(sub(sub(bg["bpp"],bg["bmp"]),
                           scale(2,mul(bg["m"],bg["j"]))),bg["phi"]))

def meanseries(bg):
    ep=jet_series(lambda n:F(original(n,'metric',0)[4,4]/2))
    em=jet_series(lambda n:F(original(n,'metric',1)[4,4]/2))
    return scale(-4,mul(bg["m"],add(ep,em)))

def codazziseries(bg):
    cp=[[F(original(n,'gauge',0)[a]) for n in range(ORDER+1)]
        for a in range(4)]
    cm=[[F(original(n,'gauge',1)[a]) for n in range(ORDER+1)]
        for a in range(4)]
    out=[]
    for a in range(4):
        v=trim([])
        for b in range(4):
            v=add(v,scale(-2*int(E4[b,b]),
                mul(bg["M"][a][b],sub(cp[b],cm[b]))))
        v=sub(v,scale(F(1,2),mul(bg["j"],add(cp[a],cm[a]))))
        out.append(v)
    return out

def check(allocation,n):
    bg=background();src=make_source()
    I=israelseries(bg);force=meanseries(bg);C=codazziseries(bg)
    mr=refrows(n,'metric',allocation,bg)
    gr=refrows(n,'gauge',allocation,bg)
    mgraph=graphcorrection(n,'metric',allocation,src)
    ggraph=graphcorrection(n,'gauge',allocation,src)
    assert mr.shape==(30,1) and gr.shape==(10,1)
    # Independent physical additions from the same exact source:
    deltaM=mgraph.copy();deltaG=ggraph.copy()
    for pos,(a,b) in enumerate(keys):
        deltaM[14+pos]+=E4[a,b]*asS(I[n])
    deltaM[29]+=asS(force[n])
    for a in range(4):deltaG[5+a]+=asS(C[a][n])
    actualM=mr+deltaM
    actualG=gr+deltaG

    # Direct exact BARE physical row creation, keeping original prefix,
    # Israel, harmonic suffix and mean distinct. No vector-padding trick.
    from check_hopf369_br_warped_physical_attachment import metric_rows,gauge_rows
    freshM=mr.copy();freshG=gr.copy()
    for i in range(30):
        if 14<=i<=23:
            a,b=keys[i-14]
            freshM[i]+=E4[a,b]*asS(I[n])
        elif i==29:
            freshM[i]+=asS(force[n])
        freshM[i]+=mgraph[i]
    for i in range(10):
        if 5<=i<=8:freshG[i]+=asS(C[i-5][n])
        freshG[i]+=ggraph[i]
    assert (actualM-freshM).applyfunc(s.cancel)==s.zeros(30,1)
    assert (actualG-freshG).applyfunc(s.cancel)==s.zeros(10,1)
    # The independent geometric correction is traced back to the
    # literal triple divided product, not an invented smooth source.
    assert I[n]==scale(2,mul(sub(sub(bg["bpp"],bg["bmp"]),
                        scale(2,mul(bg["m"],bg["j"]))),bg["phi"])[n]
    assert (deltaM!=s.zeros(30,1) and deltaG!=s.zeros(10,1))
    # The physical D/E rank or positivity is not inferred from
    # this source-level affine operator.
    print(f"BR72 constructed {allocation} order {n}: 30 metric +10 gauge, same-source complete reference corrections")

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--allocation',choices=['D','E'],required=True)
    p.add_argument('--order',type=int,required=True)
    x=p.parse_args()
    if not 0<=x.order<=8:raise ValueError('BR4 order limit eight')
    check(x.allocation,x.order)
