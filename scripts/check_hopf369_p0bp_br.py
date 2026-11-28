"""BP/BR finite exact controls: cubic extension, harmonic shell and indexed time transport.
Not a numerical PDE solve or a native kernel receipt.
"""
import sympy as s


def shell():
    j=s.symbols('j', real=True, nonzero=True)
    h=s.diag(-1,1,1,1); g=s.diag(-1,1,1,1,1)
    a=s.Matrix(s.symbols('a:4')); q=s.symbols('q')
    J=s.zeros(5);J[:4,:4]=2*j*h;J[:4,4]=a;J[4,:4]=a.T;J[4,4]=q
    n=s.eye(5)[:,4]; tr=s.trace(g*J)
    # Common adapted coordinates at one wall point, not Gaussian off wall.
    C=J*n-n*tr/2
    assert C[:4,0]==a and s.expand(C[4]-(q-8*j)/2)==0
    sol={q:8*j,**{x:0 for x in a}}; assert C.subs(sol)==s.zeros(5,1)
    # Distributional Ricci principal symbol for normal metric jump.
    R=(n*(J*n).T+(J*n)*n.T-J-n*n.T*tr)/2
    assert R[:4,:4]==-j*h and R[:4,4]==s.zeros(4,1)
    assert s.expand(R[4,4]+4*j)==0
    assert R.subs(sol)==-J.subs(sol)/2
    G=R-g*s.trace(g*R)/2
    assert G[:4,:4]==3*j*h and G[4,4]==0
    # Difference of normal Gauss constraints for arbitrary mean tensor.
    m=s.symbols('m:10'); M=s.zeros(4); k=0
    for x in range(4):
        for y in range(x,4):M[x,y]=M[y,x]=m[k];k+=1
    Kp=M+j*h/2; Km=M-j*h/2
    def Gnn(K):
        A=h*K;return (s.trace(A)**2-s.trace(A*A))/2
    tau=s.trace(h*M)
    assert s.expand(Gnn(Kp)-Gnn(Km)-3*j*tau)==0
    # C is a continuous covector. In Gaussian normal chart the
    # gauge equations have homogeneous jumps only if mean trace vanishes.
    cn,jn,ta=s.symbols('cn jn ta'); ca,ja=s.symbols('ca ja')
    mixed=(ja-2*j*ca)/2
    normal=(jn-4*j*cn)/2
    assert s.solve(mixed,ja)==[2*j*ca]
    assert s.expand(s.solve(normal-3*j*ta,jn)[0]-4*j*cn-6*j*ta)==0
    print('PASS 15 metric jump components, 5 harmonic jumps, singular Ricci/Einstein, normal Gauss and gauge transmission')


def lift():
    y,d=s.symbols('y d',positive=True)
    # Compact C3 profile (cutoff exponent 4); exact scale in the normal variable.
    p=y**3*(1-y/d)**4/6
    for k in range(3):assert s.diff(p,y,k).subs(y,0)==0
    assert s.diff(p,y,3).subs(y,0)==1
    for k in range(4):assert s.simplify(s.diff(p,y,k).subs(y,d))==0
    z=s.symbols('z');P=z**3*(1-z)**4/6
    for k in range(4):assert s.simplify(s.diff(p,y,k).subs(y,d*z)-d**(3-k)*s.diff(P,z,k))==0
    print('PASS cubic profile endpoint jets and exact d^(3-k) derivative scaling')


def transport():
    # Actual typed direction: refinement k transports both state and operator;
    # physical time t is independent. Moving frame adds a connection term.
    t=s.symbols('t');T=s.Matrix([[1,t],[0,1]]);A=s.Matrix([[0,1],[-2,0]])
    x=s.Matrix([s.Function('x')(t),s.Function('v')(t)])
    At=T*A*T.inv()+T.diff(t)*T.inv()
    assert all(s.simplify(v)==0 for v in (T*x).diff(t)-At*T*x-T*(x.diff(t)-A*x))
    # Two refinement arrows: connection obeys composition, not frozen conjugacy.
    U=s.Matrix([[1,0],[t,1]]); B=lambda V:V.diff(t)*V.inv()
    assert all(s.simplify(v)==0 for v in B(U*T)-B(U)-U*B(T)*U.inv())
    # Retain negative and zero states in the same invertible transport.
    for v in (s.Matrix([1,-1]),s.zeros(2,1),s.Matrix([-1,1])):assert T.inv()*T*v==v
    # Frozen wave interface: common trace of time derivative, flux jump lower order.
    v,pplus,pminus,k,jump=s.symbols('v pplus pminus k jump')
    assert s.expand((v*pplus-v*pminus).subs(pplus,pminus+k*jump)-v*k*jump)==0
    print('PASS k/time connection covariance, composition, signed/zero BIDI, principal flux cancellation')


def boundary():
    # AK global AdS4 base optical geometry and KK direction.
    r,b,h=s.symbols('r b h',positive=True)
    N=b*s.sqrt(1+h*h*r*r)
    g=s.diag(b*b/(1+h*h*r*r), b*b*r*r,b*b*r*r,1)
    optical=g/N**2
    assert s.simplify(optical[0,0]-1/(1+h*h*r*r)**2)==0
    assert s.simplify(optical[3,3]-1/(b*b*(1+h*h*r*r)))==0
    # At conformal end, only fibre collapses; rescaled fibre vector retains it.
    O=s.symbols('O',positive=True);Q=s.diag(-b*b,b*b,b*b,b*b,O*O)
    V=s.diag(1,1,1,1,1/O)
    assert s.simplify(V.T*Q*V-s.diag(-b*b,b*b,b*b,b*b,1))==s.zeros(5)
    print('PASS AK optical finite radial distance and weighted fibre frame reconstruction')

if __name__=='__main__':
    shell();lift();transport();boundary()
