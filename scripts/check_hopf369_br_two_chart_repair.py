#!/usr/bin/env python3
"""BR32: repair BR26 longitudinal principal kernel by freeing tangential
coordinate shift continuity and replacing it with normal-scale continuity
and three transverse plus one scalar gauge allocations as described below.
Executable comparison of boundary symbols; not a nonlinear existence proof.
"""
import sympy as s

def run():
    # Gaussian adapted frozen point. Common induced perturbation H.
    # Two decaying half-line solutions with signed normal derivatives
    # d_plus=-ell, d_minus=+ell. Unknown jump/mean beta and scale.
    ell=s.symbols('ell', nonzero=True)
    eta=s.diag(-1,1,1,1)
    z=s.Matrix(s.symbols('z0:4'))
    # Tangential frequency covector: z^T eta z=-ell²? wave normal
    # ell²=-Box_tangential symbol, so z^T eta z=-ell².
    # Use polynomial reduction rather than a choice of frequency chart.
    rel=(z.T*eta*z)[0]+ell**2
    def red(v):
        return s.rem(s.expand(v),rel,z[0])
    b=s.Matrix(s.symbols('b0:4')); q=s.Symbol('q')
    # Original BR26 continuity of beta gives H=-(z b^T+b z^T)/ell
    # from Israel principal [d_n H]=0 (common beta tangential jets cancel),
    # hence H=0; C_a jump fixes b from scale jump.
    # Normal gauge gives ell*l_plus=ell*l_minus=0 for H=0 and common beta
    # only after retaining div beta. Exact original symbol below.
    keys=[(i,j) for i in range(4) for j in range(i,4)]
    H=s.Matrix(4,4,lambda i,j:s.Symbol('h%d%d'%(min(i,j),max(i,j))))
    bp=s.Matrix(s.symbols('p0:4')); bm=s.Matrix(s.symbols('m0:4'))
    lp,lm=s.symbols('lp lm')
    variables=[H[i,j] for i,j in keys]+list(bp)+list(bm)+[lp,lm]
    L=lambda v:z*v.T+v*z.T
    tr=s.trace(eta*H)
    div=lambda v:(z.T*eta*v)[0]
    # [K]=0 principal with common H.
    israel=-2*ell*H-L(bp-bm)
    # contracted tangential Gamma jump; intrinsic terms cancel.
    ct=-z*(lp-lm)-ell*(bp+bm)
    cnplus=ell*tr/2+div(bp)-ell*lp
    cnminus=-ell*tr/2+div(bm)+ell*lm
    original=s.Matrix([israel[i,j] for i,j in keys]+list(ct)+[cnplus,cnminus]+list(bp-bm))
    A=original.jacobian(variables)
    # Kernel is in normal scale difference and common longitudinal shift.
    v=s.Matrix([0]*10+list(-z*q/(2*ell))+list(-z*q/(2*ell))+[q/2,-q/2])
    assert all(red(x)==0 for x in A*v)
    # Repair: retain 3 transverse shift conditions and replace the
    # longitudinal one by normal scale equality. Implement without
    # tangential spectral division via boundary scalar differential law.
    # This candidate still has a second longitudinal mode; test actual rank.
    # Use a fixed timelike covector chart: enforce beta spatial continuity
    # and scale continuity, freeing beta time component jump.
    repaired=s.Matrix([israel[i,j] for i,j in keys]+list(ct)+[cnplus,cnminus]+list((bp-bm)[1:4,0])+[lp-lm])
    B=repaired.jacobian(variables)
    # Exact determinant factor (no spectral sampling).
    det=s.factor(B.det(method='domain-ge'))
    # Expected nonzero except z0=0 or ell=0; Laplace Re s>0 excludes both.
    print('original determinant reduced:',red(s.factor(A.det(method='domain-ge'))))
    print('repaired determinant:',det)
    print('repaired determinant modulo wave relation:',s.factor(red(det)))
    # Require actual invertibility in the right-half-plane test cases.
    for vals in [(1,1,0,0,0),(2,2,0,0,0),(5,3,4,0,0)]:
        e,t,x,y,w=vals
        # relation z0²=ell²+spatial²; use exact Pythagorean samples below.
    for e,t,x,y,w in [(1,1,0,0,0),(3,5,4,0,0),(4,5,0,3,0)]:
        sub=dict(zip([ell,*z],[e,t,x,y,w]))
        assert rel.subs(sub)==0
        assert A.subs(sub).rank()==19
        assert B.subs(sub).rank()==20
    print('PASS exact original kernel and repaired boundary rank controls')
if __name__=='__main__':run()
