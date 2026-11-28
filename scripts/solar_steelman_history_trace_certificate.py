"""Compose actual dense trace, coefficient balls and exact defect replay.
Certifies a rational-time surrogate of the original coefficient law, conditional
on coefficient assembly correctness. Exact 2*pi clock bridge remains separate.
"""
import numpy as np
import sympy as S
from solar_steelman_history_dense_decode import read,q
from solar_steelman_history_matrix_enclosure import construct
from solar_steelman_history_polynomial_defect import bernstein_bound,defect,logarithmic_norm
from solar_steelman_history_defect_replay import replay

s=S.Symbol('s',real=True)
def restrict(piece,lo,hi):
    a,b,X=piece
    assert a<=lo<hi<=b
    old=next(iter(set().union(*(v.free_symbols for v in X))),s)
    return X.subs(old,(lo-a+(hi-lo)*s)/(b-a),simultaneous=True).applyfunc(S.expand)

def find(pieces,lo,hi):
    for p in pieces:
        if p[0]<=lo and hi<=p[1]:return restrict(p,lo,hi)
    raise ValueError('uncovered polynomial interval')

def cuts(pieces,initial,delay,T):
    pts={S.Integer(0),T}
    for a,b,_ in pieces:
        for t in (a,b):
            for k in range(3):
                z=t+k*delay
                if 0<z<T:pts.add(z)
    for a,b,_ in initial:
        for t in (a,b):
            for k in (1,2):
                z=t+k*delay
                if 0<z<T:pts.add(z)
    j=1
    while j*delay<T:
        pts.add(j*delay);j+=1
    return sorted(pts)

def certify(m,a,path,degree=8,block_path=None):
    with np.load(path,allow_pickle=False) as f:
        d,n,start,stop=map(lambda k:int(f[k]),('d','n','start','stop'))
        delay=q(f['delay']);grid=list(map(q,f['grid']));past=f['past']
    k=stop-start
    raw=list(read(path));pieces=[(lo,hi,X) for lo,hi,X,_ in raw]
    T=pieces[-1][1]
    assert grid[0]==-2*delay and grid[-1]==0
    initial=[]
    for j in range(len(grid)-1):
        P=S.Matrix(n,k,[q(v) for v in past[j].ravel()])
        Q=S.Matrix(n,k,[q(v) for v in past[j+1].ravel()])
        initial.append((grid[j],grid[j+1],P+(Q-P)*s))
    def coeff(lo,hi):return construct(m,a,lo,hi,degree)
    def hist(lo,hi):
        if hi<=0:return find(initial,lo,hi),S.Integer(0)
        assert lo>=0
        X=find(pieces,lo,hi)
        R,er=coeff(lo,hi)[3]
        return R*X,er*bernstein_bound(X,s)
    # Charge exact initial endpoint ratio mismatch rather than trusting
    # the binary64 R(0) used by the integrator.
    R0,er0=coeff(0,pieces[0][1])[3]
    X0=find(pieces,0,pieces[0][1]).subs(s,0)
    H0=initial[-1][2].subs(s,1)
    basis=S.eye(d+len(initial)*n)[:,start:stop]
    expected=basis[:d,:]
    initial_error=bernstein_bound(R0.subs(s,0)*expected-H0,s)+er0*bernstein_bound(expected,s)
    for j,p in enumerate(initial):
        initial_error=max(initial_error,bernstein_bound(p[2].subs(s,0)-basis[d+j*n:d+(j+1)*n,:],s))
    initial_state_error=bernstein_bound(X0-expected,s)
    pts=cuts(pieces,initial,delay,T);slabs=[];prev=None
    for lo,hi in zip(pts,pts[1:]):
        X=find(pieces,lo,hi)
        (A,ea),(B,eb),(C,ec),(R,er)=coeff(lo,hi)
        H1,eh1=hist(lo-delay,hi-delay);H2,eh2=hist(lo-2*delay,hi-2*delay)
        rho=defect(s,hi-lo,X,A,B,C,H1,H2,(ea,eb,ec,eh1,eh2))
        mu=logarithmic_norm(A,s,ea)
        # Bound propagated state error through ratio readback globally.
        from solar_steelman_history_exact_bounds import ratio_bounds
        r=max(1,max(ratio_bounds(c)[1] for _,_,c in a['models']))
        b=(bernstein_bound(B,s)+eb)*r;c=(bernstein_bound(C,s)+ec)*r
        jump=0 if prev is None else bernstein_bound(X.subs(s,0)-prev,s)
        slabs.append((lo,hi,mu,b,c,rho,jump));prev=X.subs(s,1)
    result=replay(delay,T,slabs,initial_state_error,(initial_error,initial_error))
    if block_path is not None:
        with np.load(block_path,allow_pickle=False) as f:
            assert int(f['start'])==start and int(f['stop'])==stop
            assert q(f['delay'])==delay and int(f['knots'])==len(initial)
            stored=S.Matrix([[q(v) for v in row] for row in f['M']])
        assert stored.shape==(d+n*len(initial),k)
        state_read=bernstein_bound(prev-stored[:d,:],s)
        history_read=S.Integer(0)
        for j,t in enumerate(grid[:-1]):
            t=T+t
            piece=next(p for p in reversed(pieces) if p[0]<=t<=p[1])
            X=restrict(piece,piece[0],piece[1]).subs(s,(t-piece[0])/(piece[1]-piece[0]))
            R,er=coeff(t,t+delay)[3]
            H=R.subs(s,0)*X
            history_read=max(history_read,bernstein_bound(H-stored[d+j*n:d+(j+1)*n,:],s)+er*bernstein_bound(X,s))
        result['state_matrix_error']=S.Rational(result['endpoint'])+state_read
        result['history_matrix_error']=r*S.Rational(result['last_window'])+history_read
    result['start']=start;result['stop']=stop;result['T']=T;result['delay']=delay
    return result

def fixture():
    p=[(S.Integer(0),S.Integer(1),S.Matrix([[s]])),(S.Integer(1),S.Integer(2),S.Matrix([[1+s]])),(S.Integer(2),S.Rational(5,2),S.Matrix([[2+s/2]]))]
    assert find(p,S.Rational(1,4),S.Rational(1,2))[0]==S.Rational(1,4)+s/4
    assert S.Rational(5,2) in cuts(p,[],S.Integer(1),S.Rational(5,2))
    print('PASS exact shifted polynomial restriction fixture')
if __name__=='__main__':fixture()
