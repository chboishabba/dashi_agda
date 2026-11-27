#!/usr/bin/env python3
"""BR32: exact BR26 longitudinal symbol, two candidate allocations.
Neither candidate is yet a constraint-preserving nonlinear IBVP.
"""
import sympy as s

def system():
    l=s.symbols('ell',nonzero=True)
    z=s.Matrix(s.symbols('z0:4')); eta=s.diag(-1,1,1,1)
    rel=(z.T*eta*z)[0]+l*l
    keys=[(i,j) for i in range(4) for j in range(i,4)]
    H=s.Matrix(4,4,lambda i,j:s.Symbol('h%d%d'%(min(i,j),max(i,j))))
    bp=s.Matrix(s.symbols('p0:4')); bm=s.Matrix(s.symbols('m0:4'))
    lp,lm=s.symbols('lp lm')
    unknown=[H[i,j] for i,j in keys]+list(bp)+list(bm)+[lp,lm]
    L=lambda v:z*v.T+v*z.T
    div=lambda v:(z.T*eta*v)[0]
    tr=s.trace(eta*H)
    israel=-2*l*H-L(bp-bm)
    ct=-z*(lp-lm)-l*(bp+bm)
    np=l*tr/2+div(bp)-l*lp
    nm=-l*tr/2+div(bm)+l*lm
    J=[israel[i,j] for i,j in keys]; db=list(bp-bm)
    # Original: four tangent gauge jumps, two normal Dirichlet, shift continuity.
    A=s.Matrix(J+list(ct)+[np,nm]+db)
    # Replacing temporal shift continuity by scale continuity DOES NOT repair it.
    bad=s.Matrix(J+list(ct)+[np,nm]+db[1:]+[lp-lm])
    # Candidate A: preserve both normal gauge conditions; release temporal
    # tangent gauge jump, enforce scale continuity instead.
    B=s.Matrix(J+list(ct[1:4,0])+[np,nm]+db+[lp-lm])
    # Candidate B: preserve all tangent gauge jumps, replace minus normal
    # gauge condition by scale continuity. Keep plus normal Dirichlet.
    C=s.Matrix(J+list(ct)+[np]+db+[lp-lm])
    return l,z,eta,rel,unknown,A,bad,B,C

def run():
    l,z,eta,rel,unknown,A,bad,B,C=system()
    red=lambda v:s.rem(s.expand(v),rel,z[0])
    a,b,c,d=[v.jacobian(unknown) for v in (A,bad,B,C)]
    q=s.Symbol('q')
    kernel=s.Matrix([0]*10+list(-z*q/(2*l))+list(-z*q/(2*l))+[q/2,-q/2])
    assert all(red(x)==0 for x in a*kernel)
    # Second allocation has independent kernel in released temporal shift.
    e=s.eye(4)[:,0]; H=-(z*e.T+e*z.T)/(2*l)
    k=s.Matrix([H[i,j] for i in range(4) for j in range(i,4)]+list(e/2)+list(-e/2)+[0,0])
    assert all(red(x)==0 for x in b*k)
    # Exact row dependency of original differential conditions on wave root.
    # np+nm = div(bp+bm)-ell*(lp-lm).
    # div(ct) = ell²*(lp-lm)-ell*div(bp+bm).
    assert red(l*(A[14]+A[15])+(z.T*eta*A[10:14,0])[0])==0
    # Determinants by direct elimination, not a numerical rank inference.
    D=[s.factor(m.det(method='domain-ge')) for m in (a,b,c,d)]
    assert red(D[0])==0 and red(D[1])==0
    assert s.factor(red(D[2])/(l**14*z[0])) in (1024,-1024,2048,-2048,4096,-4096) or red(D[2])!=0
    assert red(D[3])!=0
    print('determinants modulo wave root:',*[s.factor(red(v)) for v in D])
    cases=[(1,1,0,0,0),(3,5,4,0,0),(4,5,0,3,0),
           (s.sqrt(2),2,1,1,0),(1,s.sqrt(2),1,0,0)]
    for e0,t,x,y,w in cases:
        sub=dict(zip([l,*z],[e0,t,x,y,w]))
        assert s.simplify(rel.subs(sub))==0
        assert [m.subs(sub).rank() for m in (a,b,c,d)]==[19,19,20,20]
    # Candidate A explicit forced inverse (all 20 rows).
    rr=s.Matrix(s.symbols('r0:20'))
    dv=rr[15:19,0]; dl=rr[19]
    keys=[(i,j) for i in range(4) for j in range(i,4)]
    R=s.Matrix(4,4,lambda i,j:rr[keys.index(tuple(sorted((i,j))))])
    H=-(R+z*dv.T+dv*z.T)/(2*l)
    tr=s.trace(eta*H)
    sm=s.zeros(4,1);sm[1:4,0]=-(rr[10:13,0]+z[1:4,0]*dl)/l
    # np+nm = div(sum beta)-ell*delta scale.
    sm[0]=(z[1:4,0].dot(sm[1:4,0])-rr[13]-rr[14]-l*dl)/z[0]
    # np-nm = ell*tr+div(delta beta)-ell*sum scale.
    sl=tr+((z.T*eta*dv)[0]-rr[13]+rr[14])/l
    bp=(sm+dv)/2;bm=(sm-dv)/2
    v=s.Matrix([H[i,j] for i,j in keys]+list(bp)+list(bm)+[(sl+dl)/2,(sl-dl)/2])
    assert (c*v-rr).applyfunc(s.cancel)==s.zeros(20,1)
    # Candidate B explicit forced inverse.
    dv=rr[15:19,0];dl=rr[19]
    H=-(R+z*dv.T+dv*z.T)/(2*l)
    sm=-(rr[10:14,0]+z*dl)/l;bp=(sm+dv)/2;bm=(sm-dv)/2
    lp=s.trace(eta*H)/2+((z.T*eta*bp)[0]-rr[14])/l
    lm=lp-dl
    v=s.Matrix([H[i,j] for i,j in keys]+list(bp)+list(bm)+[lp,lm])
    assert (d*v-rr).applyfunc(s.cancel)==s.zeros(20,1)
    print('PASS two exact degenerate controls, five rank controls, two arbitrary-forcing inverse identities')
    print('A releases [C_0]; B releases C_n^-; physical subsidiary closure remains separate')

if __name__=='__main__':run()
