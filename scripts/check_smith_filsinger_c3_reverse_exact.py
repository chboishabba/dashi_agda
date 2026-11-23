"""Abstract source/geometry discriminators; no original hardware prescription."""
import sympy as S
from itertools import product

def run():
    count=0
    # Existing F05 fixed-source reverse solve, dimensionless u=Rs G.
    u=S.symbols('u', nonnegative=True)
    assert S.cancel(1-4*u/(1+u)**2-(u-1)**2/(1+u)**2)==0; count+=1
    # A source target fraction a requires a real admissible match root.
    a=S.symbols('a', positive=True)
    assert S.discriminant(a*(1+u)**2-4*u,u)==16*(1-a); count+=1
    # C3 group average, adapted from ternary phase and C3 projector owners.
    R=S.Matrix([[0,0,1],[1,0,0],[0,1,0]])
    P=(S.eye(3)+R+R**2)/3; Q=S.eye(3)-P
    for expr in (R**3-S.eye(3),P*P-P,Q*Q-Q,P*Q,R*P-P):
        assert expr==S.zeros(3); count+=1
    # A symmetry assumption is necessary for block reduction.
    A=2*S.eye(3)+R+R**2
    assert P*A*Q==S.zeros(3); count+=1
    assert P*S.diag(1,2,3)*Q!=S.zeros(3); count+=1
    # Sparse phase support: independent fast, slow, and C3 sector indices.
    def mul(x,y):
        out={}
        for (m,n,l),v in x.items():
            for (p,q,k),w in y.items():
                key=(m+p,n+q,(l+k)%3)
                out[key]=out.get(key,0)+v*w
        return {k:v for k,v in out.items() if v!=0}
    for l,k in product(range(3),repeat=2):
        assert mul({(1,1,l):1},{(-1,0,k):1})=={(0,1,(l+k)%3):1};count+=1
    # Scalar amplitude modulation need not generate azimuthal character.
    assert mul({(1,0,0):1},{(0,1,0):1})=={(1,1,0):1};count+=1
    # Half-rate pair can enter quadratic observable at twice slow rate.
    x={(0,1,1):1,(0,-1,2):1}
    assert mul(x,x)=={(0,2,2):1,(0,0,0):2,(0,-2,1):1};count+=1
    # Finite antenna/port response identification needs more than intensity.
    assert abs(S.I)**2==abs(-S.I)**2 and S.im(S.I)!=S.im(-S.I);count+=1
    print(f'{count} exact SymPy assertions PASS')
if __name__=='__main__':run()
