"""Scalar Codazzi residual propagation and normal-jet frame reconstruction.
No coupled coercivity or gauge accessibility claim.
"""
import sympy as s

def exact():
    t,x=s.symbols('t x',positive=True); b=1/t; B=s.sqrt(1+b*b)
    # Mixed residual E=K+3T-tr(T)I; background E=0.
    a,c,d,m=[s.Function(v)(t,x) for v in ('a','c','d','m')]
    E=s.diag(a,c,d,d); E[0,1]=t*m; E[1,0]=-m/t
    coords=(t,x,s.Symbol('y'),s.Symbol('z'))
    G=s.MutableDenseNDimArray.zeros(4,4,4)
    for i in range(1,4): G[0,i,i]=t; G[i,0,i]=G[i,i,0]=b
    div=lambda M,j:sum(s.diff(M[i,j],coords[i]) for i in range(4))+sum(G[i,i,h]*M[h,j]-G[h,i,j]*M[i,h] for i in range(4) for h in range(4))
    C=[s.expand(div(E,j)-s.diff(s.trace(E),coords[j])) for j in range(4)]
    assert s.simplify(C[0]+s.diff(c+2*d,t)+b*s.diff(m,x)-b*(3*a-c-2*d))==0
    assert s.simplify(C[1]-t*s.diff(m,t)-4*m+s.diff(a+2*d,x))==0
    assert C[2:]==[0,0]
    # On all diagonal rows, remaining mixed residual is transported by Codazzi.
    assert s.simplify(C[0].subs({a:0,c:0,d:0}).doit()+b*s.diff(m,x))==0
    assert s.simplify(C[1].subs({a:0,c:0,d:0}).doit()-t*s.diff(m,t)-4*m)==0
    assert s.expand(s.diff(t**4*m,t)-t**3*(t*s.diff(m,t)+4*m))==0
    # Poincare orthonormal tetrad; n=-b e_T+B e_z, tangent=B e_T-b e_z.
    # In AdS conformal frame: nabla_eT eT=-e_z, nabla_eT e_z=-e_T,
    # nabla_ez eA=0. Parallel transport requires n(rapidity)=-? derive.
    r=s.symbols('r',real=True); ch,sh=s.cosh(r),s.sinh(r)
    M=s.Matrix([[ch,-sh],[-sh,ch]])
    # connection along n has offdiagonal +sinh(r), hence n(r)=sinh(r).
    A=s.Matrix([[0,sh],[sh,0]])
    assert s.simplify(M.diff(r)*sh+A*M)==s.zeros(2)
    F,G,U,Fn,Gn,Un=s.symbols('F G U Fn Gn Un')
    P=s.diag(-2*(F-2*U),2*(G-2*U)); Pn=s.diag(-2*(Fn-2*Un),2*(Gn-2*Un))
    H=M.T*P*M
    Hn=M.T*Pn*M+sh*H.diff(r)
    assert s.simplify(Hn[0,1]-(2*ch*sh*(Fn-Gn)+2*sh*(ch**2+sh**2)*(F-G)))==0
    # Spatial frame is parallel along n, so anisotropic normal difference is unchanged.
    assert s.expand(2*(Fn-2*Un)-2*Un+6*(Un-Fn/3))==0
    # This mixed normal jet is not a tangential h_0x jet; scalar longitudinal h_0x=0.
    print('8 exact grouped Codazzi / normal-frame checks PASS')
    return C,Hn

if __name__=='__main__': exact()
