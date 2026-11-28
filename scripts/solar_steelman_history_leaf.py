"""Fixed invariant leaf for the occupied rotating delayed tangent.
Numerical structural readback; exact invariant identities from the RHS.
No full stability or nonlinear basin assertion.
"""
import numpy as np
from scipy.linalg import orth,null_space
from solar_steelman_history_section import reduced

def leaf(m,a):
    n=len(a['models']);nc=m['d']['M'].rows+m['d']['N'].rows+m['H'].rows+32
    d=nc+5*n+4;b0=m['d']['M'].rows;b1=b0+m['d']['N'].rows
    C=np.array(m['d']['C'],float);U=orth(C)
    basis=[]
    def unit(j):
        v=np.zeros(d);v[j]=1;return v
    basis.extend(unit(j) for j in list(range(b0))+list(range(b1,nc)))
    for u in U.T:
        v=np.zeros(d);v[b0:b1]=u;basis.append(v)
    for j in range(n):basis.append((unit(nc+j)+unit(nc+n+j))/np.sqrt(2))
    # Fix lower phase and weighted common phase position AND momentum.
    # Their derivatives are weighted momentum and zero, respectively.
    # Thus this is an invariant leaf, not a claim of time-shift gauge.
    w=np.r_[np.ones(n),2.]
    V=null_space(w[None,:])
    for u in V.T:
        v=np.zeros(d);v[nc+3*n:nc+4*n]=u[:-1];v[-4]=u[-1];basis.append(v)
        v=np.zeros(d);v[nc+4*n:nc+5*n]=u[:-1];v[-3]=u[-1];basis.append(v)
    basis.append(unit(d-2))
    Q=np.column_stack(basis)
    assert np.allclose(Q.T@Q,np.eye(Q.shape[1]))
    return Q

def construct(m,a,delay=.01):
    mat,R,d,n,verify=reduced(m,a,delay);verify()
    Q=leaf(m,a);assert Q.shape[0]==d
    def matrices(t):
        A,B,C=mat(t)
        return Q.T@A@Q,Q.T@B,Q.T@C
    def ratio(t):return R(t)@Q
    worst=0.
    for t in np.linspace(0,2*np.pi,17):
        A,B,C=mat(t)
        for F in (A@Q,B,C):
            worst=max(worst,np.linalg.norm(F-Q@(Q.T@F),np.inf)/max(1.,np.linalg.norm(F,np.inf)))
    assert worst<1e-9,worst
    print("PASS sampled invariant leaf tangency",d,Q.shape[1],worst,flush=True)
    return matrices,ratio,Q

def section(M,Q,n,knots):
    d,k=Q.shape;N=d+n*knots
    assert M.shape==(N,N)
    U=np.zeros((N,k+n*knots));U[:d,:k]=Q;U[d:,k:]=np.eye(n*knots)
    V=M@U;A=U.T@V
    defect=np.linalg.norm(V-U@A,np.inf)
    print("finite leaf section",A.shape,"projection defect",defect,"rho",max(abs(np.linalg.eigvals(A))),flush=True)
    print("LIMIT sampled tangency and section spectrum, not certified bounds; combined static shifts still require classification")
    return A,defect

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument("--metric",required=True);p.add_argument("--mediator",required=True);p.add_argument("--delay",type=float,default=.01);p.add_argument("--matrix");p.add_argument("--knots",type=int,default=4);x=p.parse_args()
    with open(x.metric,"rb") as f:m=pickle.load(f)
    with open(x.mediator,"rb") as f:a=pickle.load(f)
    _,_,Q=construct(m,a,x.delay)
    if x.matrix:
        with np.load(x.matrix,allow_pickle=False) as f:section(f["M"],Q,len(a["models"]),x.knots)
