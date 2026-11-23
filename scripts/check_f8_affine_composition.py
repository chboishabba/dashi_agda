"""Exact finite affine composition, receiver-control and regional ownership.
No native PDE or physical convergence claim.
"""
import sympy as s


def check():
    M=s.Matrix
    G=[M([[2,1],[0,1]]),M([[1,0],[-1,2]])]
    B=[M([1,2]),M([-2,1])]
    f=s.symbols('f0:2'); x0=M(s.symbols('x0:2'))
    q=[M(s.symbols('q%d_0 q%d_1'%(i,i))) for i in range(3)]
    d,e=s.symbols('d e'); k=[d*f[0],e*f[1],s.Integer(0)]
    x=[x0]
    for A,b,u in zip(G,B,f):x.append(A*x[-1]+b*u)
    J=sum((a.dot(z)+c for a,z,c in zip(q,x,k)),s.Integer(0))
    p=q[-1]; z=k[-1]; grad=[None,None]
    for i in (1,0):
        grad[i]=B[i].dot(p)+s.diff(k[i],f[i])
        z+=k[i]+(B[i]*f[i]).dot(p)
        p=q[i]+G[i].T*p
    assert s.expand(J-p.dot(x0)-z)==0
    assert all(s.expand(s.diff(J,u)-g)==0 for u,g in zip(f,grad))
    assert s.expand(s.diff(J,f[0])-(grad[0]-d))==d
    # Explicit homogeneous matrix composition, independent of reverse recurrence.
    H=[A.row_join(b*u).col_join(M([[0,0,1]])) for A,b,u in zip(G,B,f)]
    assert H[1]*H[0]*x0.col_join(M([1]))==x[-1].col_join(M([1]))
    # Offsets attach to receiver events, not stage transport. Partition of unity.
    w=s.symbols('w'); alpha=s.symbols('alpha'); Q=s.diag(1,0); I=s.eye(2)
    full=q[1].dot(x[1])+alpha
    retained=q[1].dot(Q*x[1])+w*alpha
    complement=q[1].dot((I-Q)*x[1])+(1-w)*alpha
    assert s.expand(full-retained-complement)==0
    assert s.expand(full-(retained+q[1].dot((I-Q)*x[1])+alpha))==-w*alpha
    print('PASS affine reverse, direct control derivative, omitted derivative, homogeneous composition, region partition, duplicated offset')

if __name__=='__main__':check()
