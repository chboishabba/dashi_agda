"""Exact scalar GN normal jets and Codazzi residual transport.
Chart-conditional, no coupled IBVP claim.
"""
import sympy as s

def exact():
    z=s.symbols('z',positive=True); B=s.sqrt(1+z*z)
    T=s.symbols('T',real=True); x=s.symbols('x',real=True); k=s.symbols('k',real=True)
    F,G,Z,J=[s.Function(a)(T,z) for a in ('F','G','Z','J')]
    u=Z+F/3
    # Poincare orthonormal basis; GN normal e_n=z(-z d_T+B d_z).
    dn=lambda v:z*(-z*s.diff(v,T)+B*s.diff(v,z))
    dt=lambda v:z*(B*s.diff(v,T)-z*s.diff(v,z))
    boost=s.eye(5); boost[0,0]=boost[4,4]=B;boost[0,4]=boost[4,0]=-z
    eta=s.diag(-1,1,1,1,1)
    zero=lambda A:A.applyfunc(s.simplify)==s.zeros(*A.shape)
    assert zero(boost.T*eta*boost-eta)
    # In conformal frame e_a=z d_a, connection along e_n is -z boost generator.
    C=s.zeros(5);C[0,4]=C[4,0]=z
    assert zero(boost.applyfunc(dn)+C*boost)
    p=s.diag(-2*(F-2*u),2*(F-2*u),2*u,2*u,2*(G-2*u))
    P=boost.T*p*boost; Pn=P.applyfunc(dn)
    # Independent covariant normal derivative before changing frame.
    assert zero(Pn-boost.T*(p.applyfunc(dn)-C.T*p-p*C)*boost)
    assert s.simplify(Pn[1,1]-Pn[2,2]+6*dn(Z))==0
    assert s.simplify(dn(F)+z*dt(F)/B-z*s.diff(F,z)/B)==0
    assert s.simplify((dn(F)+z*dt(F)/B).subs(s.diff(F,z),2*F/z+6*Z/z+J)-(2*F+6*Z+z*J)/B)==0
    # At wall z=b, tangential proper time operator is dt above; along n use dn,
    # NOT differentiate a wall-only substitution z=1/t as a normal derivative.
    # Exact mixed Codazzi residual in coordinate FRW, arbitrary residual jets.
    t=s.symbols('t',positive=True); b=1/t; q=s.I*k*b
    A,M,H,D=[s.Function(a)(t) for a in ('A','M','H','D')]
    E=s.Matrix([[A,t*M,0,0],[-M/t,H,0,0],[0,0,D,0],[0,0,0,D]])
    gamma=s.diag(-1,t*t,t*t,t*t); inv=gamma.inv(); coords=(t,x,s.Symbol('y'),s.Symbol('w'))
    # All perturbation entries carry exp(ikx); derivative by x is ik times amplitude.
    G0={(a,i,j):sum(inv[a,l]*(gamma[l,j].diff(coords[i])+gamma[l,i].diff(coords[j])-gamma[i,j].diff(coords[l]))/2 for l in range(4)) for a in range(4) for i in range(4) for j in range(4)}
    diff=lambda v,i: v.diff(t) if i==0 else (s.I*k*v if i==1 else 0)
    R=[s.expand(sum(diff(E[a,i],a)+sum(G0[a,a,c]*E[c,i]-G0[c,a,i]*E[a,c] for c in range(4)) for a in range(4))-diff(s.trace(E),i)) for i in range(4)]
    assert s.simplify(R[0]-(-s.diff(H+2*D,t)-q*M+3*b*A-b*(H+2*D)))==0
    assert s.simplify(R[1]/t-(s.diff(M,t)+4*b*M-q*(A+2*D)))==0
    assert R[2:]==[0,0]
    # If spatial rows imposed (H=D=0), residual A,M determined by Codazzi.
    r0,rx=s.symbols('r0 rx'); m=s.Symbol('m'); a=(r0+q*m)/(3*b)
    # M_t+(4b-q²/(3b))M=rx+q*r0/(3b): nonnegative damping for real k.
    rate=rx+q*a-4*b*m
    assert s.simplify(rate-(rx+q*r0/(3*b)-(4*b+k*k*b/3)*m))==0
    assert s.simplify((4*b+k*k*b/3)/b-4-k*k/3)==0
    # If temporal row also imposed, compatibility requires q M=-r0.
    assert s.simplify(R[0].subs({A:0,H:0,D:0}).doit()+q*M)==0
    print('12 grouped exact GN jet / Codazzi checks PASS')
    return P,Pn,R

if __name__=='__main__':exact()
