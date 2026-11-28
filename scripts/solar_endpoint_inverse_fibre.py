"""Endpoint-first exact rational/complex finite inverse fibre.
No empirical source or material admission. Failure to certify is not no-go.
"""
import sympy as S

def zero(A):return all(S.simplify(v)==0 for v in A)
def positive(x):
    if S.sympify(x).is_positive is not True:raise ValueError('positive scalar required')
def nonnegative(x):
    if S.sympify(x).is_nonnegative is not True:raise ValueError('nonnegative scalar required')

def fixed_source_headroom(available,passive,paid,gain):
    a,b,c,g=map(S.sympify,(available,passive,paid,gain))
    positive(a);nonnegative(b);nonnegative(c);positive(g)
    if (a-b).is_nonnegative is not True:raise ValueError('inconsistent passive cap')
    required=b+c+g
    return dict(required_useful=required,required_efficiency=required/a,
        remaining_headroom=a-required,empty=(a-required).is_negative is True)

def source_match(target):
    """Positive normalized conductance Rs G; equal-power reciprocal branches."""
    a=S.sympify(target);positive(a)
    if (a-1).is_positive:return ()
    if (1-a).is_nonnegative is not True:raise ValueError('undecided target')
    v=S.sqrt(1-a)
    return (S.simplify((1-v)/(1+v)),S.simplify((1+v)/(1-v)))

def modal_projection(source_image,receiver):
    """Signed complex complement, not unsigned power or orientation proxy."""
    z,r=map(S.Matrix,(source_image,receiver));n=(r.H*r)[0];positive(n)
    P=r*r.H/n;parallel=P*z;residual=z-parallel
    power=S.simplify((z.H*z)[0])
    return dict(parallel=parallel,residual=residual,
        amplitude=S.simplify((r.H*z)[0]/n),
        unity_overlap=zero(residual) and power.is_positive is True,
        overlap=None if power==0 else S.simplify((parallel.H*parallel)[0]/power))

def minimum_cost_fibre(A,b,G):
    """Real exact control, SPD work metric; range residual and minimum cost.
    A may be complex: real and imaginary equations are stacked separately.
    Quadratic cost is a declared control proxy, not physical paid work.
    """
    A,b,G=map(S.Matrix,(A,b,G));A=S.Matrix.vstack(S.re(A),S.im(A));b=S.Matrix.vstack(S.re(b),S.im(b))
    if G.shape!=(A.cols,A.cols) or G!=G.T or any(v.is_real is not True for v in G):raise ValueError('real symmetric work metric')
    for k in range(1,G.rows+1):positive(G[:k,:k].det())
    basis=A.columnspace();B=S.Matrix.hstack(*basis) if basis else S.zeros(A.rows,0)
    P=B*(B.T*B).inv()*B.T if basis else S.zeros(A.rows)
    y=P*b;r=b-y
    # Independent constraint rows; weighted minimum norm right inverse.
    ids=list(A.T.rref()[1]);C=A[ids,:];d=y[ids,:]
    u=G.inv()*C.T*(C*G.inv()*C.T).inv()*d if ids else S.zeros(A.cols,1)
    assert zero(A*u+r-b) and zero(A.T*r)
    N=A.nullspace()
    assert all(zero(v.T*G*u) for v in N)
    return dict(status='INHABITED' if zero(r) else 'EMPTY_EXACT_LINEAR_FIBRE',
        control=u,residual=r,null_fibre=N,minimum_cost=S.simplify((u.T*G*u)[0]),
        cost_is_declared_proxy=True)

def selection(inputs,target,degree):
    """Signed Fourier product selection, independent frequency/winding.
    Inputs tuples (fast,slow,winding); include conjugates explicitly.
    No dynamical subharmonic inference from memoryless selection.
    """
    from itertools import product
    if degree<1:raise ValueError('degree')
    return [terms for terms in product(inputs,repeat=degree) if tuple(map(sum,zip(*terms)))==tuple(target)]

def periodic_inverse(maps,observations,target,G):
    """Joint periodicity AND observation target, not separate fibre tests.
    observations=(O_k,D_k) maps pre-step state and current control to output.
    Unknown initial state is free, controls real; minimise control-only cost.
    """
    if not maps or len(maps)!=len(observations):raise ValueError('period')
    n=maps[0][0].rows;p=sum(F.cols for T,F in maps)
    M=S.eye(n);R=S.zeros(n,p);rows=[];direct=[];offset=0
    for (T,F),(O,D) in zip(maps,observations):
        E=S.zeros(F.cols,p);E[:,offset:offset+F.cols]=S.eye(F.cols)
        rows.append(O*M);direct.append(O*R+D*E)
        M=T*M;R=T*R+F*E;offset+=F.cols
    X=S.Matrix.vstack(M-S.eye(n),*rows);U=S.Matrix.vstack(R,*direct)
    b=S.Matrix.vstack(S.zeros(n,1),S.Matrix(target))
    # Project out free initial-state coordinates; real controls.
    X=S.Matrix.vstack(S.re(X),S.im(X));U=S.Matrix.vstack(S.re(U),S.im(U));b=S.Matrix.vstack(S.re(b),S.im(b))
    left=X.T.nullspace();L=S.Matrix.vstack(*(v.T for v in left)) if left else S.zeros(0,X.rows)
    f=minimum_cost_fibre(L*U,L*b,G)
    if f['status']!='INHABITED':return dict(f,initial=None,states=None)
    x,params=X.gauss_jordan_solve(b-U*f['control']);x=x.subs({v:0 for v in params});states=[x];out=[];offset=0
    for (T,F),(O,D) in zip(maps,observations):
        u=f['control'][offset:offset+F.cols,:];out.append(O*x+D*u);x=T*x+F*u;states.append(x);offset+=F.cols
    assert zero(states[-1]-states[0]) and zero(S.Matrix.vstack(*out)-S.Matrix(target))
    return dict(f,initial=states[0],states=states,monodromy=M,free_initial_fibre=X.nullspace(),physical_admission=False)
