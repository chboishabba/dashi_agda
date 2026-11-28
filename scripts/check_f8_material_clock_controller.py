"""Fixed smooth source-profile action, not an independently calibrated material.
Original F8 normalized stress units. No retarded metric encoded in couplings.
"""
import sympy as s


import math


def original_source_tensor(t, xyz):
    """Actual original compact TT source in normalized Israel stress units.
    Numeric point evaluator, not an interval enclosure. Coordinates unscaled.
    """
    eps=.04; pulse=.065
    F=lambda a:math.asinh(a)-math.sqrt(1+a*a)/a
    ds=F(t)-F(1.)
    u=[x/eps for x in xyz]; w=sum(x*x for x in u)
    if not (0<ds<pulse and w<1): return s.zeros(3)
    X=1/(1-w); f=math.exp(1-X)
    f2=(X**4-2*X**3)*f
    f3=(-X**6+6*X**5-6*X**4)*f
    f4=(X**8-12*X**7+36*X**6-24*X**5)*f
    def d4(a,b,c,d):
        i=(a,b,c,d)
        z=16*f4*math.prod(u[j] for j in i)
        for p in range(4):
            for q in range(p+1,4):
                if i[p]==i[q]: z+=8*f3*math.prod(u[i[j]] for j in range(4) if j!=p and j!=q)
        z+=4*f2*((a==b and c==d)+(a==c and b==d)+(a==d and b==c))
        return z
    def P(i,j):
        return [(i,j,1)] if i!=j else [(k,k,-1) for k in range(3) if k!=i]
    def PP(i,j,k,l):
        return sum(c*d*d4(a,b,m,n) for a,b,c in P(i,j) for m,n,d in P(k,l))
    amp=math.exp(1-1/(1-(2*ds/pulse-1)**2))
    return s.Matrix(3,3,lambda i,j:amp*(PP(i,1,1,j)-PP(i,2,2,j)-(PP(i,j,1,1)-PP(i,j,2,2))/2))


def mixed_stress(t, gi, B_inv, rho_f, K, V, Pi, charge, shear=0):
    """Exact Hilbert stress in material coordinates (phi,X)=(t,x)."""
    I=s.eye(4); fluid=s.zeros(4); clock=s.zeros(4); act=s.zeros(4)
    fluid[:,1:4]=s.Rational(4,3)*rho_f*gi[:,1:4]*B_inv
    clock[:,0]=K*gi[:,0]
    act[:,1:4]=charge*t*t*gi[:,1:4]*Pi
    X=t*t*gi[1:4,1:4]; Z=X-s.trace(X)*s.eye(3)/3
    elast=s.zeros(4); elast[:,1:4]=shear*t*t*gi[:,1:4]*Z
    return fluid-rho_f*I+clock+(-K*gi[0,0]/2-V)*I+act-charge*s.trace(Pi*X)*I/2+elast-shear*s.trace(Z*Z)*I/4


def second_stress(t,H,J,l,m,Pi,A,A2,r,muS=0):
    """Order e² mixed stress; g00=-1+e²l, g0i=e²m_i, gij=t²(I+eH+e²J).
    Controllers C±=sqrt(e)c±+e^(3/2)chi±; charge=e A+e² A2.
    """
    b=1/t; B=s.sqrt(1+b*b); rf=r*b**4; wf=4*rf/3
    K=b*b/(3*B)-wf
    df=wf*(s.trace(H*H)/4-s.trace(J)/2)
    d=s.trace(H*Pi)*A/2
    out=s.diag(-df-K*l/2+d, (df/3+K*l/2+d)*s.eye(3)-A*H*Pi+A2*Pi-muS*H)
    out[0,1:4]=wf*m.T
    out[1:4,0]=K*b*b*m
    return out


def source_shear_bound():
    """Integer bound for operator norm of actual dimensionless compact TT profile.
    f(w)=exp(1-1/(1-w)), w=|x/eps|². Time factor <=1.
    """
    X=s.symbols('X'); P=s.Integer(1); bounds={}
    for j in range(1,5):
        P=s.expand(X**2*(s.diff(P,X)-P))
        # X>=1, exp(1-X) X^m <=3 m^m (m=0 treated separately).
        bounds[j]=sum(abs(int(v))*3*max(1,m[0]**m[0]) for m,v in s.Poly(P,X).terms())
    # Fourth Cartesian derivative of f(|u|²), each |u_i|<=1.
    D4=16*bounds[4]+48*bounds[3]+12*bounds[2]
    return 36*D4


def run():
    t=s.symbols('t',positive=True); b=1/t; B=s.sqrt(1+b*b); r=s.symbols('r',positive=True)
    rho=B-1; p=-rho+b*b/(3*B); rf=r*b**4; wf=4*rf/3
    K=rho+p-wf; V=(rho-p)/2-rf/3
    checks=[]
    def ok(name,cond):
        assert cond,name; checks.append(name)
    ok('background density',s.simplify(rf+K/2+V-rho)==0)
    ok('background pressure',s.simplify(rf/3+K/2-V-p)==0)
    ok('clock equation',s.simplify(s.diff(K,t)/2+3*K/t+s.diff(V,t))==0)
    ok('radiation conservation',s.diff(rf,t)+4*rf/t==0)
    ok('positive kinetic factor',s.simplify(K-b*b*(1-4*r*b*b*B)/(3*B))==0)
    # Exact original compact TT source symbol and central normalization.
    k=s.Matrix(s.symbols('k:3',real=True)); q=(k.T*k)[0]; P=q*s.eye(3)-k*k.T; Q=s.diag(0,1,-1)
    TT=P*Q*P-P*s.trace(P*Q)/2
    ok('TT transversality',(k.T*TT).applyfunc(s.expand)==s.zeros(1,3))
    ok('TT trace',s.expand(s.trace(TT))==0)
    ok('zero mode',TT.subs(dict.fromkeys(k,0))==s.zeros(3))
    u=s.symbols('u',positive=True); f=s.exp(1-1/(1-u*u))
    ok('source centre',s.limit(s.Rational(2,5)*(s.diff(f,u,4)+4*s.diff(f,u,3)/u),u,0)==-24)
    # Actual compact source point evaluations, centre and nonzero off-axis.
    ttest=1.02; ds=math.asinh(ttest)-math.sqrt(1+ttest*ttest)/ttest-(math.asinh(1.)-math.sqrt(2.))
    temporal=math.exp(1-1/(1-(2*ds/.065-1)**2))
    centre=original_source_tensor(ttest,[0,0,0])
    ok('actual centre normalization',max(abs(float(v)) for v in centre+24*temporal*Q)<1e-10)
    rtest=.013; xx=original_source_tensor(ttest,[rtest,0,0]); U=rtest/.04
    derivatives=[s.diff(f,u,j).subs(u,U).evalf() for j in range(1,5)]
    d1,d2,d3,d4=derivatives
    axial=temporal*(s.Rational(2,5)*(d4+4*d3/U)+s.Rational(4,7)*(d4+d3/U-6*d2/U**2+6*d1/U**3)+s.Rational(1,35)*(d4-6*d3/U+15*d2/U**2-15*d1/U**3))
    ok('actual axial source vs multipoles',abs(float(xx[1,1]-axial))<1e-9)
    ok('actual compact supports',original_source_tensor(1,[0,0,0])==s.zeros(3) and original_source_tensor(ttest,[.04,0,0])==s.zeros(3))
    # Independent expansion from exact Hilbert stress, arbitrary off-diagonal jets.
    H=s.Matrix([[1,2,3],[2,4,5],[3,5,-5]])
    Pi=s.Matrix([[2,1,0],[1,-3,4],[0,4,1]])
    J=s.Matrix([[3,2,1],[2,-1,4],[1,4,2]])
    l,A,A2,muS=s.symbols('l A A2 muS'); m=s.Matrix(s.symbols('m:3')); e=s.symbols('e')
    g0=s.diag(-1,t*t*s.eye(3)); h=s.diag(0,t*t*H); j=s.diag(l,t*t*J)
    j[0,1:4]=m.T;j[1:4,0]=m
    gi0=g0.inv(); gi=gi0-e*gi0*h*gi0+e**2*(gi0*h*gi0*h*gi0-gi0*j*gi0)
    # n=sqrt(det B), radiation rho_f proportional n^(4/3).
    trunc=lambda x:s.expand(x).series(e,0,3).removeO()
    det=trunc((t*t*gi[1:4,1:4]).det())
    nd=s.trace(H*H)/4-s.trace(J)/2
    ok('volume coefficient',s.expand(det-1-2*e**2*nd)==0)
    Bi=t*t*(s.eye(3)+e*H+e**2*J)
    T=mixed_stress(t,gi,Bi,rf*(1+e**2*4*nd/3),K,V,Pi,e*A+e**2*A2,e*muS)
    T0=T.subs(e,0);T1=T.diff(e).subs(e,0);T2=T.diff(e,2).subs(e,0)/2
    zero=lambda M:M.applyfunc(s.simplify)==s.zeros(4)
    ok('full background stress',zero(T0-s.diag(-rho,p,p,p)))
    ok('full linear stress independent of H',zero(T1-s.diag(0,A*Pi)))
    ok('full quadratic constitutive stress',zero(T2-second_stress(t,H,J,l,m,Pi,A,A2,r,muS)))
    ok('covariant symmetry at order two',zero(g0*T2+h*T1+j*T0-(g0*T2+h*T1+j*T0).T))
    # Controller equations: charge C+²-C-², both kinetic terms positive.
    cp,cm=s.symbols('cp cm',real=True); xp,xm=s.symbols('xp xm'); Z=s.symbols('Z')
    d=s.symbols('d'); Cplus=d*cp+d**3*xp; Cminus=d*cm+d**3*xm
    ok('signed charge expansion',s.expand(Cplus**2-Cminus**2).coeff(d,2)==cp**2-cm**2)
    ok('second charge expansion',s.expand(Cplus**2-Cminus**2).coeff(d,4)==2*(cp*xp-cm*xm))
    L=-(Cplus**2-Cminus**2)*Z/2
    ok('controller signed variations',s.diff(L,xp)==-d**3*Cplus*Z and s.diff(L,xm)==d**3*Cminus*Z)
    # retarded scalar controller equation in eta: chi''+2chi'+q chi = ± t² c Z.
    tau=s.symbols('tau',real=True); a=s.symbols('a',positive=True); G=s.exp(-tau)*s.sinh(a*tau)/a
    ok('controller retarded kernel',s.simplify(s.diff(G,tau,2)+2*s.diff(G,tau)+(1-a*a)*G)==0)
    ok('kernel initial values',G.subs(tau,0)==0 and s.diff(G,tau).subs(tau,0)==1)
    ok('zero mode kernel',s.simplify((G.subs(a,1)-(1-s.exp(-2*tau))/2).rewrite(s.exp))==0)
    ok('resonant limit',s.limit(G,a,0)==tau*s.exp(-tau))
    # principal clock/radiation/controller energy conditions (background only).
    n=s.symbols('n',positive=True); fr=r*n**s.Rational(4,3)
    ok('radiation sound speed',s.simplify(n*s.diff(fr,n,2)/s.diff(fr,n))==s.Rational(1,3))
    # Hilbert density Hessian reciprocity for anisotropic strain coupling.
    x,y=s.symbols('x y'); U=s.Matrix([[1,2,0],[2,0,3],[0,3,1]]); W=s.Matrix([[2,0,1],[0,1,2],[1,2,-1]])
    F=s.trace(Pi*(s.eye(3)-x*U-y*W+x*y*(U*W+W*U)))
    ok('material coupling Hessian reciprocal',s.diff(F,x,y)==s.trace(Pi*(U*W+W*U)) and s.diff(F,y,x)==s.trace(Pi*(W*U+U*W)))
    # Shear penalty: -(mu/4)(C+²+C-²) ||(t² B)_TF||².
    # Frozen rest-frame quadratic principal symbol for material displacements.
    n=s.Matrix([1,2,2])/3; v=s.Matrix(s.symbols('v:3',real=True))
    Z=n*v.T+v*n.T; Z-=s.trace(Z)*s.eye(3)/3
    ok('shear directional stiffness',s.expand(s.trace(Z*Z)-2*(v.T*v)[0]-s.Rational(2,3)*(n.T*v)[0]**2)==0)
    mu=source_shear_bound()+1
    ok('integer shear bound',isinstance(mu,int) and mu>1)
    # Kinetic and spatial principal forms: w I + e A Pi and
    # (w/3) nn^T + e A Pi + e mu S (I+nn^T/3).
    # |A|<=S, mu>||Pi||. For e S small the kinetic form is positive.
    w,aa,ss,mm,L=s.symbols('w aa ss mm L',real=True)
    kin=w*s.eye(3)+e*aa*Pi
    stiff=w*n*n.T/3+e*aa*Pi+e*mm*ss*(s.eye(3)+n*n.T/3)
    ok('symmetric material principal forms',kin==kin.T and stiff==stiff.T)
    ok('baseline fluid transverse zero stiffness',stiff.subs(e,0)*s.Matrix([-2,1,0])==s.zeros(3,1))
    ok('shear does not alter original linear stress',zero(T1-s.diag(0,A*Pi)))
    print('source operator norm bound',mu-1,'shear coefficient',mu)
    print(s.__version__,len(checks),'PASS',checks)

if __name__=='__main__':run()
