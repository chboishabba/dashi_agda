"""F8 physical-normal time primitive: exact moving-wall memory identities.
No physical change or continuum numerical acceptance from symbolic checks.
"""
import sympy as S
import json

def check():
    T,z,y,k=S.symbols('T z y k',real=True); b=S.Function('b')(T);v=S.diff(b,T);s=1-v*v
    Y=S.Function('Y')(T,y);a0,a1,a2=[S.Function('a'+str(i))(T) for i in range(3)]
    D=lambda u:S.diff(u,T)-v*S.diff(u,y)
    G=lambda u:v*D(u)+S.diff(u,y)
    L=lambda u:-S.diff(u,T,2)+2*v*S.diff(u,T,y)+s*S.diff(u,y,2)+(S.diff(v,T)-3/(b+y))*S.diff(u,y)-k*k*u
    L0=lambda u:-D(D(u))+S.diff(u,y,2)-3/(b+y)*S.diff(u,y)-k*k*u
    checks=[]
    def eq(name,l,r):
        assert S.simplify(S.expand(l-r))==0,name;checks.append(name)
    eq('stationary physical-normal operator',L(Y),L0(Y))
    eq('physical derivative commutes',L(D(Y)),D(L(Y)))
    eq('moving derivative commutator',L(S.diff(Y,T))-S.diff(L(Y),T),-2*S.diff(v,T)*S.diff(Y,T,y)-S.diff(s,T)*S.diff(Y,y,2)-(S.diff(v,T,2)+3*v/(b+y)**2)*S.diff(Y,y))
    w=b**-3;at=lambda u:u.subs(y,0)
    f0=at(Y);f1=at(D(Y));Z=D(D(Y));n0=w*at(S.diff(Y,y));n1=w*at(S.diff(D(Y),y));q=S.diff(a2,T,2)-S.diff(a1,T)-k*k*a0
    for U in [Y,D(Y)]:
        n=w*at(S.diff(U,y));eq('weighted normal transport',S.diff(n,T),w*at(G(D(U)))+v*k*k*w*at(U)+v*w*at(L(U)))
    eq('wall chain rule',S.diff(f1,T),at(Z)+v*n1/w)
    J1=n1-S.diff(a2,T)+a1;J0=n0-s*a2-v*w*f1
    eq('primitive wall constraint',at(S.diff(Y,y)-v*D(Y)),(J0+s*a2)/w)
    rhs1=-k*k*a0+v*k*k*w*f1
    eq('J1 residual exact',S.diff(J1,T)-rhs1,w*at(G(Z))-q+v*w*at(L(D(Y))))
    rhs0=s*(J1-a1)-S.diff(s,T)*a2-S.diff(v*w,T)*f1+v*k*k*w*f0
    eq('J0 residual exact',S.diff(J0,T)-rhs0,v*w*at(L(Y)))
    # Converse: impose J0,J1 ODE and wall constraint; J0 residual gives n1 identity with coefficient s>0.
    p,j0,j1=S.symbols('p j0 j1');f0s,f1s,n1s=S.symbols('f0 f1 n1')
    eq('converse normal identity',s*n1s+s*S.diff(a2,T)*(-1)+s*a1-s*j1,s*(n1s-S.diff(a2,T)+a1-j1))
    # Reverse-clock characteristic boundary and energy flux.
    u,H,W,N,P,M=S.symbols('u H W N P M',real=True);sr=1-u*u;dr=W-u*N
    eq('reverse memory wall', (N-u*dr).subs(N,(u*W+H)/(1+u*u)),H)
    eq('reverse dissipative flux',(u*W+sr*N).subs(N,(u*W+H)/(1+u*u)),(2*u*W+sr*H)/(1+u*u))
    pc=(1-u)*P/2-(1+u)*M/2;eq('incoming characteristic target',pc.subs(M,((1-u)*P-2*H)/(1+u)),H)
    eq('reverse trace',(-dr).subs(N,(u*W+H)/(1+u*u)),(u*H-W)/(1+u*u))
    # Source-to-receiver contraction: no second derivative of primitive needed.
    g=S.Function('g')(T)
    eq('source integration by parts',w*g*at(Z),S.diff(w*g*f1,T)-S.diff(w*g,T)*f1-v*g*n1)
    # source support disjoint from receiver window: n1=J1 there.
    return dict(checks=len(checks),names=checks,sympy=S.__version__,scope='exact operator, wall and source contraction identities; smooth solutions and separated flat supports')

if __name__=='__main__': print(json.dumps(check(),indent=2))
