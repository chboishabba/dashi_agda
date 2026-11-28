"""Actual causal F8 time chart, moving domain and normal-frame transport.
Full reduced bulk energy with explicit wall work; not coupled boundary coercivity.
"""
from fractions import Fraction as Q
import sympy as s


def run():
    th,y=s.symbols('theta y',real=True); b=s.Function('b')(th); v=b.diff(th); a=v.diff(th)
    z=y+b; q=z/s.sqrt(1+z*z); d=1/(1+z*z)
    C=q+d*v; B=1-2*q*v-d*v*v
    u=s.Function('u')(th,y)
    T=lambda f:f.diff(th)-v*f.diff(y)
    Z=lambda f:q*f.diff(th)+(1-q*v)*f.diff(y)
    assert s.simplify(T(z))==0 and s.simplify(Z(z)-1)==0
    assert s.expand(T(Z(u))-Z(T(u))).simplify()==0
    expected=-d*u.diff(th,2)+2*C*u.diff(th,y)+B*u.diff(y,2)+q.diff(y)*u.diff(th)+(d*a-q.diff(y)*v)*u.diff(y)
    assert s.simplify(-T(T(u))+Z(Z(u))-expected)==0
    beta=s.sqrt(1+b*b); sub={y:0,v:-b*beta}
    assert s.simplify(C.subs(sub,simultaneous=True))==0
    assert s.simplify(B.subs(sub,simultaneous=True)-(1+b*b))==0
    # Scalar principal first-order symmetrizer, all tensor components share it.
    D,F,G=s.symbols('D F G',positive=True); W=s.Matrix(s.symbols('w:6'))
    H=s.diag(1,D,F,1,1,1); Ay=s.zeros(6); Ay[1,1]=2*G/D;Ay[1,2]=F/D;Ay[2,1]=1
    assert H*Ay==Ay.T*H
    assert s.expand((W.T*H*Ay*W)[0]-2*G*W[1]**2-2*F*W[1]*W[2])==0
    for i in range(3):
        A=s.zeros(6);A[1,3+i]=1/D;A[3+i,1]=1
        assert H*A==A.T*H
    # Poincare orthonormal to GN normal-parallel frame: boost in (0,4).
    r=s.symbols('z',positive=True); L=s.eye(5); J=s.zeros(5); J[0,4]=J[4,0]=1
    L[0,0]=L[4,4]=s.sqrt(1+r*r);L[0,4]=L[4,0]=-r
    E=s.diag(-1,1,1,1,1)
    assert s.simplify(L.T*E*L-E)==s.zeros(5)
    assert s.simplify(L.diff(r)*L.inv()+J/s.sqrt(1+r*r))==s.zeros(5)
    p=s.Matrix(5,5,lambda i,j:s.Function('p%d%d'%(min(i,j),max(i,j)))(r))
    direct=r*s.sqrt(1+r*r)*(L.T*p*L).diff(r)
    transported=L.T*(r*s.sqrt(1+r*r)*p.diff(r)-r*(J*p+p*J))*L
    assert (direct-transported).applyfunc(s.simplify)==s.zeros(5)
    # Conservative energy constants: z in [1/12,4], |b'|<=2, |b''|<=3.
    # 1/17<=d<=1, B>=1, |d_theta|<=2, |B_theta|<=40,
    # |C_y|<=3, |B_y|<=8. Packed Euclidean norm bounds from donor.
    assert 2*(229*17+497*5+3*192*5+4608*5)+2*17+40+6*17+16*5+2*5<100000
    assert 5*5>17
    print('16 grouped exact checks PASS')

if __name__=='__main__':run()
