"""Exact triangular phase/reservoir identities; actual graph check on trusted mediator.
No numerical full-system stability claim.
"""
import sympy as S

def certify(parent,order):
    n=len(order)
    D=S.zeros(n+1,n)
    for k,j in enumerate(order[1:]):
        D[parent[j],k]=-1;D[j,k]=1
    D[0,n-1]=2;D[n,n-1]=-1
    v=S.Matrix([1]*n+[2])
    assert D.T*v==S.zeros(n,1) and D.rank()==n
    K=D*D.T
    assert K*v==S.zeros(n+1,1)
    # With equal positive damping gamma, C=gamma*K. On v-perp all
    # stiffness eigenvalues are positive, so r^2+gamma*lambda*r+lambda
    # has strictly negative real parts. Common mode is free rotor.
    T,w,t=S.symbols('T w t',positive=True)
    A=S.Matrix([[0,1],[0,0]]);M=S.eye(2)+T*A
    assert (M-S.eye(2)).rank()==1 and (M-S.eye(2))**2==S.zeros(2)
    s=S.sqrt(2)*S.cos(2*t)
    assert S.integrate(s*s,(t,0,2*S.pi))==2*S.pi
    assert S.trigsimp(S.diff(s*s,t)+4*S.sin(4*t))==0
    print("PASS graph rank",D.rank(),"common inertia",v.dot(v),"phase Jordan block",M)
    print("reservoir multiplier",S.exp(-2*S.pi/w),"at 100",S.N(S.exp(-2*S.pi/100),16))
    print("LIMIT fixed periodic feed breaks continuous phase/time-shift symmetry of full RHS; retain phase forcing and core Jordan audit")

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument("--mediator");args=p.parse_args()
    if args.mediator:
        with open(args.mediator,"rb") as f:a=pickle.load(f)
        certify(a['parent'],a['order'])
    else:
        print("Path fixture only; actual graph requires trusted mediator")
        certify({j:j-1 for j in range(1,48)},list(range(48)))
