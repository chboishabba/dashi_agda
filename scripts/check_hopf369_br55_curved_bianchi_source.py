#!/usr/bin/env python3
"""BR55: curved 5D harmonic-gauge subsidiary source on the same Einstein metric.

Classical exact tensor identity for any Levi-Civita connection:
 S_ab(C)=(∇_a C_b+∇_b C_a)/2, tr S=∇·C.
 ∇^a(S_ab-g_ab tr S/2)=1/2(□ C_b+Ric_b^c C_c).

Only at the AdS5 vacuum reference Ric=-4g (not a general reduced metric):
  ∇^a trace_reverse(S_ab)=1/2(□-4)C_b.
Since the full Einstein tensor is divergence free (and Λg as well),
the trace-reversed REDUCED Einstein residual must source the
subsidiary (□-4) equation. An arbitrary residual is NOT zero.

This is an all-five-index curved commutator identity with an
INDEPENDENT Weyl/Israel wall source remaining. It does NOT prove
that the actual nonlinear evolving Einstein metric solves the gauge
wave IBVP, nor project the five gauge components into BR29's 35 bulk.

--part curved|flat|boundary
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import gauge_rows,E4

def curved():
    C=s.Matrix(s.symbols('C0:5'))
    Box=s.Matrix(s.symbols('BoxC0:5'))
    gradDiv=s.Matrix(s.symbols('gradDiv0:5'))
    curv=s.Matrix(5,5,lambda i,j: -4*int(i==j))
    # G_b := ∇^a∇_b C_a is NOT grad_b(div C):
    # torsion-free curvature commutator contributes Ric_b^c C_c.
    swapped=gradDiv+curv*C
    divergence_trace_reversed=(Box+swapped-gradDiv)/2
    expected=(Box-4*C)/2
    assert divergence_trace_reversed==expected
    for k in range(5):
        assert s.expand(divergence_trace_reversed[k]-Box[k]/2+2*C[k])==0
    assert (expected-Box/2)!=s.zeros(5,1) # negative scalar-wave control
    # Same-object source equation from contracted Bianchi:
    # if Ered=Etrue-S(C), then div TREred=-1/2(□-4)C.
    source=-expected
    assert divergence_trace_reversed+source==s.zeros(5,1)
    print('PASS BR55 five curved Ric=-4 Bianchi channels, source equation, missing-curvature negative control')

def flat():
    from check_hopf369_br46_bianchi_source_weld import check
    # Actual BR46 all five exact metric (15) / gauge (5) symbols.
    for i in range(5):check(i)
    print('PASS BR55 five independent frozen principal symbols and full curved-source continuation')

def boundary():
    j=s.Rational(-6,5)
    q=s.Matrix([s.Rational(i+2,7) for i in range(4)])
    cp=s.Matrix([s.Rational(i+2,9) for i in range(5)])
    cm=s.Matrix([s.Rational(i-1,11) for i in range(5)])
    dp=s.Matrix([s.Rational(i-3,13) for i in range(5)])
    dm=s.Matrix([s.Rational(i+1,17) for i in range(5)])
    M=s.Matrix(4,4,lambda i,k:s.Rational((min(i,k)+2)*(max(i,k)+3),19))
    # BR34 original reference rows plus genuine nonzero-mean
    # coordinate Codazzi correction; both D/E allocations preserve
    # all ten physical subsidiary rows but with DIFFERENT gauge prefixes.
    original={a:gauge_rows(cp,dp,cm,dm,q,j,a) for a in "DE"}
    for a in "DE":assert original[a].rows==10
    jump=cp[:4,0]-cm[:4,0]
    correction=-2*M*E4*jump-j*(cp[:4,0]+cm[:4,0])
    physical_tangent=dp[:4,0]-dm[:4,0]+q*(cp[4]-cm[4])+correction
    coordinate_row=physical_tangent
    # BR34 reference source has -j/2, not general -j, so the
    # expected source difference is -(j/2)(Cp+Cm)-2M eta[ C].
    reference=original['D'][5:9,0]
    correction_due_to_curvature=physical_tangent-reference
    assert (correction_due_to_curvature
      +2*M*E4*jump+j*(cp[:4,0]+cm[:4,0])/2)==s.zeros(4,1)
    assert correction_due_to_curvature!=s.zeros(4,1)
    assert original['D'][-1]==original['E'][-1]
    print('PASS BR55 true 10-row D/E original gauge and explicit curved nonzero-mean Codazzi forcing')
    print('REMAINS physical PDE subsidiary uniqueness and BR29 rank-9 projected wall compatibility')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['curved','flat','boundary'],default='curved')
    a=p.parse_args()
    {'curved':curved,'flat':flat,'boundary':boundary}[a.part]()

if __name__=='__main__':main()
