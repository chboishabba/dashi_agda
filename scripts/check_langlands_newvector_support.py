"""R332: exact original type-character exclusion and bounded Cartan/covector geometry."""
from itertools import product
from random import Random
from collections import Counter
import sympy as s


def v3(x):
    x=s.Rational(x)
    if not x:return float('inf')
    a,b=abs(int(x.p)),int(x.q);v=0
    while a%3==0:a//=3;v+=1
    while b%3==0:b//=3;v-=1
    return v


def power(i):return s.Integer(3)**i


B=s.Matrix([[6,21],[-7,-15]])/9
X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])
Q=[B**i*X*s.diag(power(7-2*i),power(6-2*i)) for i in range(4)]
q=s.diag(*Q) # interleaved original (1,pi) pairs; permutation of R306 grouped chart
E=s.zeros(2);E[1,0]=1
rad=[1,2,1,1]


def in_rad(T):
    return all(v3(T[i,j])>=rad[2*(i%2)+(j%2)] for i,j in product(range(T.rows),range(T.cols)))


def exponent(a):
    return 4 if v3(a)>=-2 else -2*v3(a)-1


def main():
    a=s.Symbol('a');U=s.Matrix([[1,a],[0,1]])
    T=s.simplify(Q[0]*U*E*U.inv()*Q[0].inv())
    assert s.simplify(T-s.Matrix([[a+s.Rational(2,9),(9*a+2)**2/21],[-s.Rational(7,27),-a-s.Rational(2,9)]]))==s.zeros(2)
    assert s.expand(s.trace(B*T)/3+(243*a*a-81*a+19)/243)==0
    rng=Random(332);shears=[s.Integer(0)]+[power(e)*c for e in range(-20,11) for c in (1,2,-1,4)]
    checks=0
    for a in shears:
        R=Q[0]*s.Matrix([[1,a],[0,1]]);Y=power(exponent(a))*R*E*R.inv()
        assert in_rad(Y) and Y*Y==s.zeros(2) and (s.eye(2)+Y).det()==1
        assert v3(s.trace(B*Y)/3)==-1;checks+=1
    Y=power(4)*Q[0]*E*Q[0].inv()
    assert Y==s.Matrix([[18,s.Rational(108,7)],[-21,-18]])
    assert s.trace(B*Y)/3==-s.Rational(19,3)
    # Cross-block coupling: the rank-one obstruction is valid only when ALL blocks lie in the radical.
    coupled=Counter()
    beta=s.diag(B,B,B,B);Ei=s.zeros(8);Ei[1,0]=1
    for _ in range(48):
        a=rng.choice(shears);u=s.eye(8);u[0,1]=a
        for i,j in [(0,2),(1,3),(0,5),(1,7)]:u[i,j]=rng.choice([0,1,-1])*power(rng.randrange(-12,13))
        z=q*u;Y=power(exponent(a))*z*Ei*z.inv()
        assert Y**2==s.zeros(8) and v3(s.trace(beta*Y)/3)==-1
        coupled['excluded' if in_rad(Y) else 'not_excluded']+=1
    assert all(coupled.values()) and len(coupled)==2
    # Principal congruence containment: the upper block crossing a gap of level c.
    gap_checks=0
    for i in range(1,8):
        for c in (1,3,20):
            ds=[0]*i+[c]* (8-i);D=s.diag(*[power(d) for d in ds]);Di=D.inv()
            for r,j in product(range(i),range(i,8)):
                N=s.zeros(8);N[r,j]=rng.choice([1,2,4,9]);Z=Di*N*D
                assert all(v3(e)>=c for e in Z);gap_checks+=1
            N=s.zeros(8);N[i-1,i]=1
            D=s.diag(*([1]*i+[power(c-1)]*(8-i)))
            assert v3((D.inv()*N*D)[i-1,i])==c-1
    # Covector reduction and exact entrywise integrality on actual dimension 8.
    covector_checks=0;kernel_checks=0
    for _ in range(48):
        c=20;ds=sorted(rng.randrange(0,24) for _ in range(8));ds=[d-ds[0] for d in ds]
        D=s.diag(*[power(d) for d in ds]);Di=D.inv();k=s.eye(8);h=s.eye(8)
        for M in (k,h):
            for _ in range(6):
                i,j=rng.sample(range(8),2);A=s.eye(8);A[i,j]=rng.randrange(-2,3);M[:,:]=M*A
        v=h.inv()[7,:];j=s.eye(8);i,l=rng.sample(range(8),2);j[i,l]=power(rng.choice([0,3,20,20+ds[-1]]))
        z=Di*k.inv()*j*k*D;y=h.inv()*z*h
        assert (all(v3(x)>=0 for x in y)==all(v3(x)>=0 for x in z))
        assert (all(v3(y[7,l]-int(l==7))>=c for l in range(8))==all(v3(e)>=c for e in v*z-v))
        covector_checks+=1
        M=max(3,c+ds[-1]);N=s.zeros(8);N[i,l]=power(M);z=Di*k.inv()*N*k*D
        assert all(v3(x)>=c for x in z);kernel_checks+=1
    # Finite linear projection toy: image mod 3^1, compare all lifts mod 3^2.
    projected=set();direct=set()
    for a,b in product(range(9),repeat=2):
        if (a+3*b)%9==0:direct.add((a%3,b%3))
    for a,b in product(range(3),repeat=2):
        if any((a+3*i+3*(b+3*j))%9==0 for i,j in product(range(3),repeat=2)):projected.add((a,b))
    assert direct==projected=={(0,0),(0,1),(0,2)}
    print(dict(shear_exclusions=checks,coupled_controls=dict(coupled),gap_checks=gap_checks,covector_checks=covector_checks,kernel_checks=kernel_checks,identity_phase_exponent='-19/3',toy_projection=len(projected)))


if __name__=='__main__':main()
