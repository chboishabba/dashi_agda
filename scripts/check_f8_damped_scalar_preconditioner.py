"""F8 frozen scalar Robin: root-adapted preconditioner, not a warped IBVP.
Uses the existing scalar_matrix owner. Analytic estimates in the roadmap.
"""
from fractions import Fraction as Q
import sympy as s
import mpmath as mp

GAMMA=10**7

def root(K,k):
    if not k: return mp.mpf(0)
    lo=mp.mpf(0); hi=(2*K*k*k)**(mp.mpf(1)/3)
    for _ in range(240):
        m=(lo+hi)/2
        if m*m*(m+8*K)>2*K*k*k: hi=m
        else: lo=m
    return (lo+hi)/2


def matrices(t,z,k):
    b=1/t; beta=mp.sqrt(1+b*b); w=b**4/12; K=b*b/(3*beta)-w
    la=mp.sqrt(z*z+k*k); d=z*z+k*k/3; a=2/beta+6*beta
    I=mp.eye(3); u=mp.matrix([[-z/2,1j*k,-3*z/2]])
    c=mp.matrix([10*z,6j*k,2*z])*K/la**2
    Z=mp.matrix([[-1,0,3]])*la/(la+a)
    D=mp.matrix([[k*k/2,1j*z*k,-3*z*z/2]])/d
    V=mp.matrix([[-z/2,1j*k/3,-z/2]])*1j*k/d
    B=mp.matrix(3,3)
    for i in range(3):
        B[0,i]=-2/beta*I[0,i]-6*w*D[i]-5*K*I[0,i]+Z[i]/beta
        B[1,i]=-2*beta*I[1,i]-6*w*V[i]
        B[2,i]=-2*beta*I[2,i]-2*w*D[i]-K*I[0,i]-beta*Z[i]
    F=la**3+8*K*la**2-2*K*k*k
    inv0=(I+c*u*la**2/F)/la
    return la,K,B,la*I-c*u+B,inv0,F


def norm(A):return max(sum(abs(A[i,j]) for j in range(A.cols)) for i in range(A.rows))


def exact():
    L,r,K,k,z=s.symbols('L r K k z',positive=True)
    f=L**3+8*K*L**2-2*K*k*k
    assert s.expand(f.subs(k*k,r*r*(r+8*K)/(2*K))-(L-r)*(L*L+(r+8*K)*L+r*(r+8*K)))==0
    u=s.Matrix([[-z/2,s.I*k,-3*z/2]]); c=K*s.Matrix([10*z,6*s.I*k,2*z])/L**2
    assert s.expand(((u*c)[0]*L**2)+K*(8*z*z+6*k*k))==0
    assert s.expand((L**3+8*K*z*z+6*K*k*k).subs(z*z,L*L-k*k)-f)==0
    # Sherman-Morrison, without assuming a real Laplace parameter.
    I=s.eye(3); den=L-(u*c)[0]
    assert ((L*I-c*u)*(I+c*u/den)/L-I).applyfunc(s.cancel)==s.zeros(3)
    # Far from acoustic resonance vs near acoustic resonance.
    assert Q(2,3)*Q(27,40)-Q(1,10)>Q(1,4)
    assert Q(2,3)-Q(1,4)>Q(3,8)
    # Conservative far/near preconditioned perturbation bounds.
    assert Q(4801*133,GAMMA)<Q(1,10)
    assert Q(218*3,2*GAMMA)+Q(941760,GAMMA)<Q(1,10)
    return 8


def run():
    mp.mp.dps=85; checks=exact(); cases=0; peak=mp.mpf(0); loss=[]
    for t in map(mp.mpf,(1,3,12)):
        b=1/t; K=b*b/(3*mp.sqrt(1+b*b))-b**4/12
        for k in map(mp.mpf,(0,10**8,10**16,10**24,10**36)):
            rr=root(K,k)
            zs=[mp.mpc(GAMMA),mp.mpc(GAMMA,k),mp.mpc(GAMMA,k/mp.sqrt(3))]
            if k>rr: zs.append(mp.mpc(GAMMA,mp.sqrt(k*k-rr*rr)))
            for z in zs:
                la,kk,B,N,inv0,F=matrices(t,z,k)
                p=norm(inv0*B); peak=max(peak,p)
                assert p<mp.mpf('.1')
                assert norm(inv0*(N-B)-mp.eye(3))<mp.mpf('1e-35')
                rhs=mp.matrix([1,2,-3]); sol=mp.lu_solve(N,rhs)
                assert norm(N*sol-rhs)<mp.mpf('1e-35')
                cases+=1
            if t==1 and k>rr:
                la,kk,B,N,inv0,F=matrices(t,zs[-1],k)
                loss.append((str(k),mp.nstr(norm(inv0)*abs(la),12)))
    print('exact checks',checks,'diagnostic cases',cases,'max preconditioned residual norm',mp.nstr(peak,12))
    print('near surface resonance normalized inverse:',loss)
    print('PASS; frozen flat-normal comparison only')

if __name__=='__main__':run()
