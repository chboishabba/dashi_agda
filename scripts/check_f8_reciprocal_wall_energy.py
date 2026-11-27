"""Exact variable-FRW signed bulk/wall work; not positive physical energy."""
import sympy as s
from itertools import combinations_with_replacement


def run():
    t=s.symbols('t',positive=True); b=1/t; B=s.sqrt(1+b*b)
    K,w=s.symbols('K w',real=True); g=s.diag(-1,1,1,1); I=s.eye(4)
    k0=-1/B; ks=-B; L=s.diag(k0,ks,ks,ks); tau=s.trace(L)
    h=s.Matrix(4,4,lambda i,j:s.Symbol(f'h{min(i,j)}{max(i,j)}'))
    ht=s.Matrix(4,4,lambda i,j:s.Symbol(f'v{min(i,j)}{max(i,j)}'))
    z,zt=s.symbols('z zt'); T=s.Matrix(4,4,lambda i,j:s.Symbol(f'T{i}{j}'))
    pair=lambda a,c:s.trace(g*a*g*c)
    H=s.trace(g*h); Ht=s.trace(g*ht); A=s.trace(L*g*h); At=s.trace(L*g*ht)
    dh=-6*g*T+2*s.trace(T)*g+h*L-L*h+z*g*L
    dz=s.trace(g*dh)-2*tau*z+2*A
    bulk=pair(ht,dh)+zt*dz-(Ht+zt)*(s.trace(g*dh)+dz)/2
    alg=z*At+zt*A-tau*z*zt-Ht*A
    assert s.expand(bulk+6*pair(ht,g*T)-alg)==0
    # Metric-only constitutive stress, with full mixed symmetry correction.
    l=h[0,0]; j=s.trace(h[1:,1:]); m=h[1:,0]
    lt=ht[0,0]; jt=s.trace(ht[1:,1:]); mt=ht[1:,0]
    Tm=s.diag(w*j/2-K*l/2,(-w*j/6+K*l/2)*s.eye(3))
    Tm[0,1:]=w*m.T;Tm[1:,0]=K*m
    # Replace K+w by actual rho+p in Israel reciprocity.
    form=s.expand(-6*pair(ht,g*Tm)+alg)
    form=s.expand(form.subs(K,b*b/(3*B)-w))
    # Reconstruct the exact boundary potential from the symmetric Hessian.
    coords=[h[i,j] for i,j in combinations_with_replacement(range(4),2)]+[z]
    rates=[ht[i,j] for i,j in combinations_with_replacement(range(4),2)]+[zt]
    coeff=s.Matrix([s.diff(form,a) for a in rates]); M=coeff.jacobian(coords)
    assert (M-M.T).applyfunc(s.simplify)==s.zeros(11)
    potential=(s.Matrix(coords).T*M*s.Matrix(coords))[0]/2
    assert s.simplify(sum(s.diff(potential,a)*v for a,v in zip(coords,rates))-form)==0
    # Gauge/Israel forcing is affine, keeps the normal and trace row.
    r=s.Matrix(4,4,lambda i,j:s.Symbol(f'r{min(i,j)}{max(i,j)}')); c=s.symbols('c')
    dh2=dh+r;dz2=s.trace(g*dh2)-2*tau*z+2*A+c
    work2=pair(ht,dh2)+zt*dz2-(Ht+zt)*(s.trace(g*dh2)+dz2)/2
    assert s.expand(work2-bulk-pair(ht,r)+Ht*s.trace(g*r)-(zt-Ht)*c/2)==0
    # Full variable-time material work, using a periodic/decaying spatial integral.
    # One spatial dimension is sufficient for the scalar identities, with vector
    # sums restored componentwise; all transverse terms are retained below.
    x,y,q=s.symbols('x y q',real=True); xyz=(x,y,q)
    K=s.Function('K')(t);w=s.Function('w')(t);u=s.Function('u')(t,*xyz)
    v=s.Matrix([s.Function(f'v{i}')(t,*xyz) for i in range(3)])
    m=s.Matrix([s.Function(f'm{i}')(t,*xyz) for i in range(3)])
    l=s.Function('l')(t,*xyz);j=s.Function('j')(t,*xyz)
    dot=lambda a:a.diff(t); grad=lambda a:s.Matrix([b*a.diff(c) for c in xyz]); div=lambda a:sum(b*a[i].diff(c) for i,c in enumerate(xyz))
    inner=lambda a,c:(a.T*c)[0]; Q=l+j/3; alpha=3*b+dot(K)/(2*K)
    Fu=-(dot(l)+dot(j))/2+div(m)-alpha*l
    Fv=dot(m)-grad(Q)/2
    Pu=K*(dot(l)+dot(j))*dot(u)-2*K*inner(dot(m),grad(u))+u*(-3*b*K*dot(l)+(dot(K)+3*b*K)*dot(j))
    Bu=-3*b*K*l+(dot(K)+3*b*K)*j
    Xu=-2*K*inner(m,grad(u))+u*Bu
    Ru=2*(dot(K)+2*b*K)*inner(m,grad(u))-(dot(K)+3*b*K)*(l+j)*dot(u)-u*(dot(Bu)-(-3*b*K*dot(l)+(dot(K)+3*b*K)*dot(j))+3*b*Bu)
    assert s.expand(Pu+2*K*dot(u)*Fu-dot(Xu)-3*b*Xu-Ru-2*K*div(dot(u)*m))==0
    Pv=w*dot(Q)*div(v)-2*w*inner(dot(m),dot(v)-b*v)
    Xv=w*Q*div(v)+2*b*w*inner(m,v)
    Rv=2*b*w*Q*div(v)-2*b*w*inner(m,dot(v))+4*b*b*w*inner(m,v)
    assert s.expand((Pv+2*w*inner(dot(v),Fv)-dot(Xv)-3*b*Xv-Rv+w*div(Q*dot(v))).subs(dot(w),-4*b*w))==0
    # Signed fibre pairing inertia: 4 time-space directions negative,
    # trace block one negative. This is NOT a positive energy.
    eta=s.diag(-1,1,1,1,1); ids=list(combinations_with_replacement(range(5),2)); basis=[]
    for i,j in ids:
        p=s.zeros(5);p[i,j]=p[j,i]=1;basis.append(p)
    G=s.Matrix(15,15,lambda i,j:s.trace(eta*basis[i]*eta*basis[j])-s.trace(eta*basis[i])*s.trace(eta*basis[j])/2)
    eig=G.eigenvals(); assert sum(n for e,n in eig.items() if e>0)==10 and sum(n for e,n in eig.items() if e<0)==5
    assert G.det()!=0
    print('8 grouped exact checks PASS; signed fibre inertia',eig)
    print('metric wall potential Hessian symmetric; variable-time clock/fluid work reciprocal')

if __name__=='__main__':run()
