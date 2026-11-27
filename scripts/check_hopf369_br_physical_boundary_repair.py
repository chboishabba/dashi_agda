#!/usr/bin/env python3
"""BR33: physical mean Israel force in the reduced boundary allocation.
Exact forced principal boundary inverses and gauge subsidiary inverse.
The variable-coefficient metric/gauge IBVP is not proved by this script.
"""
import sympy as s


def run():
    l,T,C=s.symbols('ell T C',nonzero=True)
    z=s.Matrix(s.symbols('z0:4')); eta=s.diag(-1,1,1,1)
    div=lambda v:(z.T*eta*v)[0]
    q=div(z); rel=q+l*l
    red=lambda v:s.rem(s.expand(v),rel,z[0])
    keys=[(i,j) for i in range(4) for j in range(i,4)]
    H=s.Matrix(4,4,lambda i,j:s.Symbol('h%d%d'%(min(i,j),max(i,j))))
    bp=s.Matrix(s.symbols('bp0:4')); bm=s.Matrix(s.symbols('bm0:4'))
    lp,lm=s.symbols('lp lm'); dv=bp-bm; sm=bp+bm; dl=lp-lm; sl=lp+lm
    v=s.Matrix([H[i,j] for i,j in keys]+list(bp)+list(bm)+[lp,lm])
    # Exact finite-interval flat DtN: endpoints share induced H.
    # Signed jump derivative = -T*(sum endpoints), mean derivative = -C*jump/2.
    # T=ell*tanh(ell L/2), C=ell*coth(ell L/2); half-line T=C=ell.
    J=-2*T*H-z*dv.T-dv*z.T
    ct=-z*dl-T*sm
    np=T*s.trace(eta*H)/2+div(bp)-(T*sl+C*dl)/2
    nm=-T*s.trace(eta*H)/2+div(bm)+(T*sl-C*dl)/2
    # tau_plus+tau_minus = -div(beta_plus+beta_minus).
    F=-div(sm)
    # D keeps all tangent gauge continuity and plus normal gauge.
    D=s.Matrix([J[i,j] for i,j in keys]+list(ct)+[np]+list(dv)+[F])
    # E keeps both normal gauge conditions and spatial tangent gauge continuity.
    E=s.Matrix([J[i,j] for i,j in keys]+list(ct[1:4,0])+[np,nm]+list(dv)+[F])
    r=s.Matrix(s.symbols('r0:20')); d=r[15:19,0]
    R=s.Matrix(4,4,lambda i,j:r[keys.index(tuple(sorted((i,j))))])
    h=-(R+z*d.T+d*z.T)/(2*T); tr=s.trace(eta*h)
    def pack(b,p,a,j):
        return s.Matrix([h[i,j] for i,j in keys]+list((b+d)/2)+list((b-d)/2)+[(a+p)/2,(a-p)/2])
    # D: physical mean force and tangent gauge jump determine scale difference.
    p=(T*r[19]-div(r[10:14,0]))/q
    b=-(r[10:14,0]+z*p)/T
    a=tr+(div(b+d)-C*p-2*r[14])/T
    vd=pack(b,p,a,0)
    assert (D.jacobian(v)*vd-r).applyfunc(s.cancel)==s.zeros(20,1)
    # E: normal gauge sum and mean force determine scale difference directly.
    p=-(r[13]+r[14]+r[19])/C
    b=s.zeros(4,1);b[1:4,0]=-(r[10:13,0]+z[1:4,0]*p)/T
    b[0]=(z[1:4,0].dot(b[1:4,0])+r[19])/z[0]
    a=tr+(div(d)-r[13]+r[14])/T
    ve=pack(b,p,a,0)
    assert (E.jacobian(v)*ve-r).applyfunc(s.cancel)==s.zeros(20,1)
    dd=s.factor(D.jacobian(v).det(method='domain-ge'))
    de=s.factor(E.jacobian(v).det(method='domain-ge'))
    print('physical metric determinants:',dd,de)
    assert s.cancel(dd/(T**14*q)) in (s.Rational(2)**14,-s.Rational(2)**14)
    assert s.cancel(de/(T**14*C*z[0])) in (s.Rational(2)**14,-s.Rational(2)**14)
    # Exact gauge subsidiary, same signed normal and Gauss/Codazzi conventions.
    # In Gaussian trace coordinates:
    # [d_n C_a]+D_a[C_n]-2[K_a^b C_b]=0;
    # [d_n C_n]-div[C_a]-[tau C_n]=0 if mean physical tau=0.
    # Reference K±=±j*h/2; tau±=±2j. Retain lower-order j terms
    # in the boundary operator (flat interior DtN comparison only).
    j=s.symbols('j',real=True)
    cp=s.Matrix(s.symbols('cp0:4'));cm=s.Matrix(s.symbols('cm0:4'))
    u,w=s.symbols('u w'); gv=s.Matrix(list(cp)+list(cm)+[u,w])
    cg=cp-cm; cs=cp+cm; ng=u-w; ns=u+w
    tangent=-(T+j)*cs+z*ng
    normal=-(T+2*j)*ns-div(cg)
    GD=s.Matrix([u]+list(cg)+list(tangent)+[normal])
    GE=s.Matrix([u,w]+list(cg[1:4,0])+list(tangent)+[normal])
    f=s.Matrix(s.symbols('f0:10'))
    # D: plus normal Dirichlet, all tangent continuity, jump derivatives.
    cgd=f[1:5,0]; nsd=-(f[9]+div(cgd))/(T+2*j)
    ud=f[0];wd=nsd-ud; csd=(z*(ud-wd)-f[5:9,0])/(T+j)
    gvd=((csd+cgd)/2).col_join((csd-cgd)/2).col_join(s.Matrix([ud,wd]))
    assert (GD.jacobian(gv)*gvd-f).applyfunc(s.cancel)==s.zeros(10,1)
    # E: both normal Dirichlet; temporal tangent jump is solved by Gauss.
    cge=s.zeros(4,1);cge[1:4,0]=f[2:5,0]
    ue,we=f[0],f[1]
    cge[0]=(f[9]+(T+2*j)*(ue+we)+z[1:4,0].dot(cge[1:4,0]))/z[0]
    cse=(z*(ue-we)-f[5:9,0])/(T+j)
    gve=((cse+cge)/2).col_join((cse-cge)/2).col_join(s.Matrix([ue,we]))
    assert (GE.jacobian(gv)*gve-f).applyfunc(s.cancel)==s.zeros(10,1)
    gd=s.factor(GD.jacobian(gv).det(method='domain-ge'));ge=s.factor(GE.jacobian(gv).det(method='domain-ge'))
    print('gauge determinants:',gd,ge)
    assert s.cancel(gd/((T+j)**4*(T+2*j))) in (1,-1,16,-16)
    assert s.cancel(ge/((T+j)**4*z[0])) in (1,-1,16,-16)
    # Gauge Gauss normal derivative identity with arbitrary noncommuting mean K.
    M=s.Matrix(4,4,lambda a,b:s.Symbol('m%d%d'%(min(a,b),max(a,b))))
    M[0,0]=sum(M[i,i] for i in range(1,4)); I=s.eye(4)
    ap=eta*M+j*I/2;am=eta*M-j*I/2
    G=lambda A:(s.trace(A)**2-s.trace(A*A))/2
    assert s.expand(G(ap)-G(am))==0
    assert s.trace(ap)==2*j and s.trace(am)==-2*j
    assert (2*(ap.T*cp-am.T*cm)-2*M*eta*cg-j*cs).applyfunc(s.expand)==s.zeros(4,1)
    # Right-half-plane exact samples, includes zero tangential spatial frequency.
    for e,t,x,y,w0 in [(1,1,0,0,0),(3,5,4,0,0),(4,5,0,3,0)]:
        sub=dict(zip([l,*z],[e,t,x,y,w0]));sub.update({T:e,C:e,j:-s.Rational(6,5)})
        assert rel.subs(sub)==0
        assert D.jacobian(v).subs(sub).rank()==20 and E.jacobian(v).subs(sub).rank()==20
        assert GD.jacobian(gv).subs(sub).rank()==10 and GE.jacobian(gv).subs(sub).rank()==10
    print('PASS all forced metric and gauge inverse identities, finite-interval symbolic transfer, physical Gauss/Codazzi allocation')
    print('D: mean force + all tangent gauge continuity + one normal Dirichlet; E: mean force + both normal Dirichlet + spatial tangent gauge continuity')
    print('Frozen boundary inverse only; variable-coefficient subsidiary uniqueness and reduced evolution still require estimates.')

if __name__=='__main__':run()
