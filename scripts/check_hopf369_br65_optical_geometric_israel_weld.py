#!/usr/bin/env python3
"""BR65: actual BR34 Israel rows vs BR60/61 full moving-wall Israel geometry.

At the original two-face Gaussian reference, let k+=j/2,k-=-j/2
(or arbitrary k+,k- with j=k+-k-). Perturb with common graph phi and
original normalized BR34 fields H±, beta±, ell±, vx±.
Raw physical metric normal derivative is px_ab+2k H_ab; tangent
mixed derivative is q_a beta_b, for the Fourier/jet reference sector.

Full nonlinear shape first variation from BR60:
 dK± = K_BR34± - Hess(phi) +(k±²+b±'')phi eta.
Induced matching is H+ +2k+phi eta=H-+2k-phi eta, so
 H+ - H- = -2j phi eta.

Define the ORIGINAL BR34 Israel 10-row block
 J_BR34=2(K+ - K-) - j(H+ + H-)
and the full geometric reference row R=2(dK+ -dK-) -2j dh_common.
Then EXACTLY, on the matched induced wall:
    R - J_BR34 = 2(b+''-b-'')phi eta.
No k, q, beta, ell or Hess(phi) terms are discarded; their
cancellations follow from actual original source and compatibility.
If b+''=b-'' the BR34 Israel reference IS the geometric R.
Otherwise the explicitly missing warp-acceleration/tension variation
must be paid as a physical source, not equated away.

The full Israel linearization is then 1/2 trace_reverse(R)
+3 dj eta as in BR64. This source equality is only the ten Israel
rows; the other BR34 D/E gauge and mean-force rows remain independent.

Checks independently import original metric_side and metric_rows.
No CI or Agda kernel acceptance claimed.
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import metric_side,metric_rows,E4,trace4,dec

def tensor(H,b,l):
    return H.row_join(b).col_join(b.T.row_join(s.Matrix([[2*l]])))

def source():
    phi,dj=s.symbols("phi dj",real=True)
    kp,km=s.symbols("kp km",real=True)
    bpp,bmp=s.symbols("bpp bmp",real=True)
    j=kp-km
    q=s.Matrix(s.symbols("q0:4"))
    # Independent OFF-matched metric source on plus side, then actual
    # induced-metric matching constructs the minus-side H (not guessed).
    H=s.Matrix(4,4,lambda a,b:s.Symbol("H%d%d"%(min(a,b),max(a,b))))
    Hm=H+2*j*phi*E4
    beta=s.Matrix(s.symbols("bp0:4"))
    betam=s.Matrix(s.symbols("bm0:4"))
    lp,lm=s.symbols("lp lm")
    xp=s.Matrix(4,4,lambda a,b:s.Symbol("xp%d%d"%(min(a,b),max(a,b))))
    xm=s.Matrix(4,4,lambda a,b:s.Symbol("xm%d%d"%(min(a,b),max(a,b))))
    pp=tensor(H,beta,lp);pm=tensor(Hm,betam,lm)
    ppx=tensor(xp,s.zeros(4,1),0)
    pmx=tensor(xm,s.zeros(4,1),0)
    Hp,bp,Kp,taup,_,_=metric_side(pp,ppx,q,kp)
    Hn,bm,Km,taum,_,_=metric_side(pm,pmx,q,km)
    # BR34 uses k=j/2 and -j/2: first verify its original J block
    # for this actual mean-free reference, then generalize algebra.
    J=2*(Kp-Km)-j*(Hp+Hn)
    fullshape=2*(Kp-Km+(bpp-bmp+kp*kp-km*km)*phi*E4) -2*j*(H+2*kp*phi*E4)
    difference=(fullshape-J-2*(bpp-bmp)*phi*E4).applyfunc(s.expand)
    assert difference==s.zeros(4)
    assert (H+2*kp*phi*E4-Hm-2*km*phi*E4)==s.zeros(4)
    # Correct sign: without induced matching, the cancelled H difference
    # reappears. This is a mandatory source compatibility hypothesis.
    Hwrong=Hm+s.eye(4)
    Jwrong=2*(Kp-Km)-j*(H+Hwrong)
    assert (fullshape-Jwrong-2*(bpp-bmp)*phi*E4)!=s.zeros(4)
    # True physical trace-reversal with independently nonzero dj.
    tr=lambda T:trace4(T)
    I=fullshape/2-E4*tr(fullshape)/2+3*dj*E4
    fromI=2*((I-3*dj*E4)-E4*tr(I-3*dj*E4)/3)
    assert (fromI-fullshape).applyfunc(s.expand)==s.zeros(4)
    return pp,ppx,pm,pmx,q,j,phi,bpp,bmp,J,fullshape,I

def check(part):
    pp,px,pm,mx,q,j,phi,bpp,bmp,J,R,I=source()
    # Original BR34 applies exactly at k+=j/2, k-=-j/2:
    # source() has independent k±; match the mean to zero for the row
    # comparison. All expressions are already symbolic.
    if part in ("reference","both"):
        kplus,kminus=s.symbols("kp km",real=True)
        from check_hopf369_br_warped_physical_attachment import keys
        # The general k± formula is checked by source(); use
        # the zero-mean specialization explicitly in the exact original.
        j0=s.symbols("j0",real=True)
        subs={kplus:j0/2,kminus:-j0/2}
        orig=metric_rows(pp.subs(subs),px,pm.subs(subs),mx,q,j0,"D")
        expected=s.Matrix([J[a,b].subs(subs) for a,b in keys])
        assert (orig[14:24,0]-expected).applyfunc(s.expand)==s.zeros(10,1)
        for alloc in "DE":
            actual=metric_rows(pp.subs(subs),px,pm.subs(subs),mx,q,j0,alloc)
            assert (actual[14:24,0]-expected).applyfunc(s.expand)==s.zeros(10,1)
        print("PASS BR65 ORIGINAL D/E Israel 10 reference rows, exact source match")
    if part in ("geometry","both"):
        assert (R-J-2*(bpp-bmp)*phi*E4).applyfunc(s.expand)==s.zeros(4)
        assert R==R.T
        assert (I-3*s.symbols("dj")*E4-(R-E4*trace4(R))/2).applyfunc(s.expand)==s.zeros(4)
        # Nonzero warp acceleration mismatch is REAL.
        special=(R-J).subs({bpp:1,bmp:0,phi:1})
        assert special==2*E4
        assert (R-J).subs({bpp:0,bmp:0})==s.zeros(4)
        print("PASS BR65 nonlinear two-face shape ↔ BR34 Israel, residual 2[b'']phi eta")
        print("PASS induced-metric matching, nonzero warp acceleration negative control")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=["reference","geometry","both"],default="geometry")
    check(p.parse_args().part)
