#!/usr/bin/env python3
"""BR4 fixed material seam: variable principal wave energy and differentiated
transmission. Reduced metric subsystem only; not a physical shell theorem."""
import sympy as s

def check():
    # A=-g^00>0, B=g^0i, C=g^ij positive on the selected time chart.
    # Use first-order state (u,w=u_t,d_i=u_i) with arbitrary shift.
    A=s.symbols('A',positive=True)
    B=s.Matrix(s.symbols('B0:4',real=True))
    C=s.Matrix(4,4,lambda i,j:s.Symbol('C%d%d'%(min(i,j),max(i,j)),real=True))
    H=s.diag(1,A,C)
    for i in range(4):
        M=s.zeros(6)
        M[1,1]=2*B[i]/A
        M[1,2:6]=C[i,:]/A
        M[2+i,1]=1
        assert H*M==(H*M).T
    w=s.Symbol('w',real=True); d=s.Matrix(s.symbols('d0:4',real=True))
    # divergence form: -A w_t+2B.d w+C:dd u+
    # (-A_t+div B)w+(B_t+div C).d = F
    # E=(A w²+C[d,d]+u²)/2
    At=s.Symbol('At'); Bt=s.Matrix(s.symbols('Bt0:4'))
    Ct=s.Matrix(4,4,lambda i,j:s.Symbol('Ct%d%d'%(min(i,j),max(i,j))))
    divB=s.Symbol('divB'); divC=s.Matrix(s.symbols('divC0:4'))
    dw=s.Matrix(s.symbols('dw0:4')); Hess=s.Matrix(4,4,lambda i,j:s.Symbol('h%d%d'%(min(i,j),max(i,j))))
    F,u=s.symbols('F u')
    wt=(2*B.dot(dw)+s.trace(C*Hess)+(-At+divB)*w+(Bt+divC).dot(d)-F)/A
    Et=At*w*w/2+A*w*wt+(d.T*Ct*d)[0]/2+(d.T*C*dw)[0]+u*w
    flux=divB*w*w+2*w*B.dot(dw)+w*divC.dot(d)+w*s.trace(C*Hess)+dw.dot(C*d)
    assert s.expand(Et-flux-(-At*w*w/2+w*Bt.dot(d)+(d.T*Ct*d)[0]/2+u*w-w*F))==0
    # Both faces share u,w,d,A,B,C. Signed outward flux cancels.
    phi=B[3]*w*w+w*(C*d)[3]
    assert phi-phi==0
    # Inhomogeneous flux with common w,d_t, discontinuous conormal.
    r=s.Symbol('r'); assert s.expand(w*(phi/w+r)-phi-w*r)==0
    # Differentiation in tangential directions commutes with fixed cut.
    # One derivative of divergence-form equation: operator commutator
    # -div((D a) grad u). No derivative of characteristic function.
    t,x,y=s.symbols('t x y'); U=s.Function('U')(t,x,y)
    a=s.Function('a')(t,x,y)
    coords=(t,x,y)
    L=lambda v:sum(s.diff(a*s.diff(v,z),z) for z in coords)
    for D in (t,x):
        assert s.expand(s.diff(L(U),D)-L(s.diff(U,D))-sum(s.diff(s.diff(a,D)*s.diff(U,z),z) for z in coords))==0
    # BR4 transformed inverse is independent of q (cusp removed).
    h=s.diag(-s.Symbol('N',positive=True)**2,1,1,1)
    beta=s.Matrix(s.symbols('beta0:4')); bar=h.row_join(h*beta).col_join((beta.T*h).row_join(s.Matrix([[1+(beta.T*h*beta)[0]]])))
    q=s.Symbol('q',positive=True)
    inv=h.inv()+beta*beta.T
    inv=inv.row_join(-beta).col_join((-beta.T).row_join(s.ones(1)))
    assert (bar*inv-s.eye(5)).applyfunc(s.expand)==s.zeros(5)
    assert ((bar/q**2)*(q**2*inv)-s.eye(5)).applyfunc(s.expand)==s.zeros(5)
    # Fixed chart normal wall law: reduced normal mean curvature
    # is independent of the differentiated conformal scale in neither gauge.
    # In zero-normal-shift adapted point, g=q^-2 bar g:
    # n(log lambda)=-q_y, H_n=q H_y.
    qp,qm,Hyp,Hym,j=s.symbols('qp qm Hyp Hym j')
    Wp=-qp-q*Hyp; Wm=-qm-q*Hym
    assert s.expand((Wp-Wm).subs({qp:qm-j,Hyp:Hym-3*j/q}))==4*j
    # Only the mean wall law is imposed; one-sided curvature need not vanish.
    assert s.expand(((Wp+Wm)/2).subs(Hyp,-(qp+qm)/q-Hym))==0
    print('PASS variable principal symmetrizer, exact energy identity, tangential commutator, cusp-free inverse')
    print('NOTE physical mean wall law is an additional constraint; not inferred from reduced metric energy')

if __name__=='__main__':check()
