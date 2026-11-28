"""Exact normalization and Ward discriminator on the configured side-four carrier.
The raw bare vertices are not derivatives of the full background Hessian.
The transported pure-gauge calculation is a covariance reference: it transports
 the configured constant-mode projector too, and is not a generic CMP109 proof.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s
from check_ym_p33_configured_contractions_20261119 import N,O,neg,weight,local_contraction
from check_ym_p33_bubble_20261119 import bubble_coordinate
from check_ym_anchored_fp_20261119 import evaluate
from check_ym_p33_fourier_vertices_20261119 import SITES

def audit():
    p=(1,0,0,0);left=(0,1,p);right=(0,1,neg(p))
    t=local_contraction(left,right);b=bubble_coordinate(left,right)
    fp=evaluate(0,p,0);h=F(2*N,3)
    assert t[1]==b[1]==0
    residual=(t[0]-b[0])/2+fp+h
    assert residual==F(-271,3)
    print('raw longitudinal T, B, FP, bare Haar, residual:',t[0],b[0],fp,h,residual)
    # H(g)=exp(gR) H0 exp(-gR). In a Fourier eigenbasis:
    # H_prime[i,j]=(lambda_j-lambda_i)R[i,j];
    # H_second[i,i]=2 sum_j (lambda_i-lambda_j)R[i,j]R[j,i].
    # Sum paired ordered terms before trace. The identity holds for every
    # pair of positive configured eigenvalues (including the zero mode).
    a,c=s.symbols('a c', positive=True)
    tad_pair=2*(a-c)/a+2*(c-a)/c
    bubble_pair=2*(c-a)*(a-c)/(a*c)
    assert s.cancel(tad_pair-bubble_pair)==0
    checks=0
    for k in SITES:
        q=tuple((x+y)%4 for x,y in zip(k,p))
        a0,c0=1/weight(k),1/weight(q)
        assert 2*(a0-c0)/a0+2*(c0-a0)/c0==2*(c0-a0)*(a0-c0)/(a0*c0)
        checks+=1
    print('PASS transported pure-gauge configured trace-log pair cancellation:',checks)
    # The bare Haar trace is a vacuum constant, not by itself an external
    # background Hessian; a right translation preserves Haar measure.
    print('OPEN actual CMP109 constrained Hessian derivative, transported completion and source normalization, physical beta')
if __name__=='__main__':audit()
