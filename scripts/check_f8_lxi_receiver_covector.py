"""Exact corrected receiver injection weld to #1530's native adjoint chronology."""
import sympy as s

def check():
    h,t,S,Se,L,X=s.symbols('h t S Se L X', nonzero=True)
    a,b,c,p,q,r=s.symbols('a b c p q r')
    z=s.Matrix([a,b,c,p,q,r,L,X]); HT=(c-a)/(2*h); HTT=(a-2*b+c)/h**2
    HTt=q; HTTt=(r-p)/(2*h)
    W=[]
    for v,j in ((HT,HTT),(HTt,HTTt)):
        A=S*S*j+Se*v
        W.extend([-(A+L)/(4*t*t),-(A+2*S*v-L)/(2*t*t)])
    J=s.Matrix(W).jacobian(z)
    assert s.simplify(J*z-s.Matrix(W))==s.zeros(4,1)
    for i in (0,2):
        assert s.simplify(W[i+1]-2*W[i]-(L-S*(HT if i==0 else HTt))/t**2)==0
        assert s.simplify(W[i]-W[i].subs(L,X)-(X-L)/(4*t*t))==0
    assert J[:,7]==s.zeros(4,1)
    # Scalar noncommutative RK chain is verified below with exact rational matrices.
    B0=s.Matrix([[1,2],[0,1]]);B1=s.Matrix([[2,0],[3,1]]);Bh=s.Matrix([[1,1],[-1,2]])
    I=s.eye(2); G=I/3+s.Rational(2,3)*Bh*(s.Rational(3,4)*I+B1*B0/4)
    lam=s.Matrix(s.symbols('l0:2')); l2=s.Rational(2,3)*Bh.T*lam;l1=B1.T*l2/4
    assert G.T*lam==lam/3+s.Rational(3,4)*l2+B0.T*l1
    # Additive observations at an intermediate time require an injection.
    e0=s.Matrix([1,3]);r0=s.Matrix([-2,1]);r1=s.Matrix([4,-1]);w0=s.Matrix([1,2]);w1=s.Matrix([3,-1]);w2=s.Matrix([2,4])
    e1=B0*e0+r0;e2=B1*e1+r1;L2=w2;L1=B1.T*L2+w1;L0=B0.T*L1+w0
    assert (w0.dot(e0)+w1.dot(e1)+w2.dot(e2))==L0.dot(e0)+L1.dot(r0)+L2.dot(r1)
    print('PASS corrected four receiver covectors, dual Weyl identities, axial negative controls, noncommuting RK reverse and observation injections')
if __name__=='__main__':check()
