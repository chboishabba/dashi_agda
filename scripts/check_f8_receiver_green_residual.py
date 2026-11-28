"""F8 W2-W4: original weighted Green, energy and C1 reconstruction algebra.
Manufactured checks only; no original-trajectory error enclosure or kernel claim.
"""
import json
import sympy as S


def check():
    T,y,k=S.symbols('T y k', real=True)
    b=S.Function('b')(T); v=S.diff(b,T); sig=1-v*v; w=(b+y)**-3
    u=S.Function('u')(T,y); p=S.Function('p')(T,y)
    W=S.diff(u,T); N=S.diff(u,y)
    F=lambda a:-S.diff(a,T)+v*S.diff(a,y)
    G=lambda a:v*S.diff(a,T)+sig*S.diff(a,y)
    L=lambda a:-S.diff(a,T,2)+2*v*S.diff(a,T,y)+sig*S.diff(a,y,2)+(S.diff(v,T)-3/(b+y))*S.diff(a,y)-k*k*a
    J=lambda a,c:w*(p*a(u)-u*a(p))
    checks=[]
    def eq(label,a,c):
        assert S.simplify(S.expand(a-c))==0,label
        checks.append(label)
    eq('weighted divergence',w*L(u),S.diff(w*F(u),T)+S.diff(w*G(u),y)-w*k*k*u)
    eq('signed Green',w*(p*L(u)-u*L(p)),S.diff(J(F,None),T)+S.diff(J(G,None),y))
    P=W+(1-v)*N; M=W-(1+v)*N
    E=w*(W*W+sig*N*N+k*k*u*u)/2
    eq('energy residual',S.diff(E,T),S.diff(w*W*G(u),y)+w*(3*v/(2*(b+y))*(P*M-k*k*u*u)+S.diff(v,T)*(P*P-M*M)/4-W*L(u)))
    # Scalar flux lift, with actual variable v and weight; no fitted emitter.
    g=S.Function('g')(T); chi=S.Function('chi')(y); h=y*chi*g/sig
    eq('exact lower flux lift',G(h).subs(y,0).subs(chi.subs(y,0),1),g)
    # Manufactured exact Green integral including nonzero wall, top and time terms.
    sub={b:2-T/4}; z=2-T/4+y
    a=z**3*(1+T+y+T*y); d=z**3*(2-T+y*y+T*y)
    def inst(expr):return S.cancel(expr.subs({u:a,p:d}).subs(sub).doit())
    area=lambda f:S.integrate(S.integrate(S.cancel(f),(y,0,1)),(T,0,1))
    edge=lambda f,x:S.integrate(S.cancel(f),(x,0,1))
    jt=inst(J(F,None)); jy=inst(J(G,None)); volume=area(inst(w*(p*L(u)-u*L(p))))
    time=edge(jt.subs(T,1)-jt.subs(T,0),y); top=edge(jy.subs(y,1),T); lower=edge(jy.subs(y,0),T)
    obs=edge(inst(w*u*G(p)).subs(y,0),T); flux=edge(inst(w*p*G(u)).subs(y,0),T)
    eq('full signed boundary accounting',volume,time+top-lower)
    eq('reverse wall observation',obs,volume-time-top+flux)
    assert all(x!=0 for x in (time,top,flux,obs));checks.append('nonzero boundary guards')
    # Tensor Hermite basis: C1 reconstruction from U, W, N and one mixed jet.
    x=S.symbols('x'); H=[1-3*x*x+2*x**3,3*x*x-2*x**3,x-2*x*x+x**3,-x*x+x**3]
    for j,hj in enumerate(H):
        for i,val in enumerate([hj.subs(x,0),hj.subs(x,1),S.diff(hj,x).subs(x,0),S.diff(hj,x).subs(x,1)]):eq('Hermite trace',val,int(i==j))
    # Continuous observer coefficients a2,a1,a0, exact integration by parts.
    a2,a1,a0=[S.Function(n)(T) for n in ('a2','a1','a0')]
    eq('window integration by parts',a2*S.diff(u,T,2)+a1*W-k*k*a0*u,(S.diff(a2,T,2)-S.diff(a1,T)-k*k*a0)*u+S.diff(a2*W+(a1-S.diff(a2,T))*u,T))
    # Original direct/SMS off-shell row identity, independently symbolic.
    t=S.symbols('t',positive=True); A,B,D,Ey,Y,Lap=S.symbols('A B D Ey Y Lap')
    bv=1/t; vv=-1/S.sqrt(1+t*t); ss=1-vv*vv; acc=t**3/(1+t*t)**2
    scale=S.sqrt(1+t*t)/t; jj=-1/(t*S.sqrt(1+t*t))
    wall=vv*A+ss*D; res=-B+2*vv*Ey+ss*Y+(acc-3/bv)*D+Lap
    box=-B+2*vv*Ey+ss*Y+acc*D+Lap
    normal=vv*vv*B+2*vv*ss*Ey+ss*ss*Y-vv*vv*acc*D
    direct=bv*bv*(-normal/(2*ss)+box/6); sms=-bv*bv*(scale*scale*B+(jj+2*scale)*A-Lap)/2
    eq('original direct SMS affine identity',direct-sms+(bv+bv**3/2)*wall+bv*bv*res/3,0)
    return dict(checks=len(checks),sympy=S.__version__,manufactured=dict(volume=str(volume),time=str(time),top=str(top),lower=str(lower),wall_flux=str(flux),observation=str(obs)),scope='exact algebra and manufactured Green signs; no actual numerical residual enclosure')


if __name__=='__main__':print(json.dumps(check(),indent=2))
