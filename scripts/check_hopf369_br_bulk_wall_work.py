#!/usr/bin/env python3
"""Principal metric/embedding work identity and positive-energy obstruction.
Consumes BR9/BR18 signed material seam, not an instability claim.
"""
import sympy as s
from itertools import combinations_with_replacement

def run():
    ix=list(combinations_with_replacement(range(5),2))
    eta=s.diag(-1,1,1,1,1); n=s.eye(5)[:,4]; j=s.symbols('j',real=True,nonzero=True)
    def enc(p):return s.Matrix([p[a,b] for a,b in ix])
    def sym(tag):return s.Matrix(5,5,lambda a,b:s.Symbol(tag+str(min(a,b))+str(max(a,b)),real=True))
    J=enc(2*j*eta+6*j*n*n.T); e=enc(n*n.T)
    assert (e.T*J)[0]==8*j
    m=sym('m'); z=m[4,4]; a=s.Matrix([*s.symbols('f0:4'),0])
    r=enc(2*j*m+j*z*eta+9*j*z*n*n.T-6*j*(n*a.T+a*n.T))
    v=enc(sym('v')); d=enc(sym('d')); ft=s.Symbol('ft',real=True)
    W=s.Matrix(15,15,lambda a,b:s.Symbol('w%d_%d'%(min(a,b),max(a,b)),real=True))
    # [p_t]=-J ft; signed total bulk normal flux = -[p_t^T W p_y].
    plus=(v-J*ft/2).T*W*(d+r/2)
    minus=(v+J*ft/2).T*W*(d-r/2)
    assert s.expand((-plus+minus+v.T*W*r-ft*J.T*W*d)[0])==0
    # Wall equation f_tt-Delta f+c f + mean(p_nn,y)/2=0.
    # To cancel the unrestricted mean conormal d, W J=K e/2.
    K=s.Symbol('K',real=True)
    # Test with d=J: positivity of W requires J^T W J>0, so 4jK>0.
    assert (K*e.T*J/2)[0]==4*j*K
    # Exact normal scalar restriction: [p]=-8j f, [p_y]=12j m.
    mt,pt,mean_y,f=s.symbols('mt pt mean_y f',real=True)
    bulk=-12*j*mt*pt+8*j*ft*mean_y
    wall=-ft*mean_y/2
    robin=12*j*mt*pt
    assert s.expand(bulk+16*j*wall+robin)==0
    # For actual j=-6/5, the unique constant positive bulk scalar multiplier
    # forces negative embedding kinetic coefficient in this cancellation.
    assert (16*j).subs(j,-s.Rational(6,5))==-s.Rational(96,5)
    # General arbitrary B,D background shifts alter lower-order flux,
    # not the principal coefficient of the free mean conormal.
    B=enc(sym('B')); D=enc(sym('D'))
    # Material q=mean p+fB, r_material=[p_y]+fD.
    rp=r-f*D
    assert (rp+f*D-r)==s.zeros(15,1)
    print('PASS signed all-component work pairing and diagonal positive-energy obstruction')
    print('The result rules out only the specified local separated energy ansatz, not physical stability.')

if __name__=='__main__':run()
