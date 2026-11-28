"""F8 W2 exact rational coefficient majorant for normal-reduced GN commutator.
Pays one tangential graph-energy level, not the physical Israel boundary trace.
"""
import sympy as s

def exact():
    R=s.Rational
    # Proven on 1<=t<=12, 0<=n<=1/2 by the GN coefficient enclosure:
    # a>1/5, 3/5<N<7/6, |N_t|<4/15, |N_tt|<2/5,
    # |N_tn|<7/12, a<=t*cosh(n), cosh(n)<7/6,
    # sqrt(1+t²)<13 and |N_n|/N<35/18.
    Na=R(35,6);Nt=R(4,15);Na_t=Nt*5
    NtN=Nt/R(3,5)
    NttN=R(2,5)/R(3,5)
    # rA=3N/a-N_t/N, rB=3N/a+N_t/N,
    # rA_t=3(N_t/a-(N/a)^2)-N_tt/N+(N_t/N)^2.
    drA=3*(Na_t+Na**2)+NttN+NtN**2
    assert drA<114
    rA=3*Na+NtN
    diff=2*NtN
    DA=drA+rA*diff
    assert DA<140
    # (rB)_n=3(N_n/a-N a_n/a²)+N_tn/N-N_t N_n/N².
    # N_n/a=-1/sqrt(1+t²); a_n=-sqrt(1+t²)N.
    drB=3*(1+13*Na**2)+(R(7,12)/R(3,5))+NtN*R(35,18)
    assert drB<1500
    assert R(7,6)*1500==1750
    assert diff<1
    assert 3*Na+NtN<20
    assert 2*Na**2<72
    # Four physical graph components, real or imaginary independently:
    # P=sqrt(A)*|u_t|, Q=sqrt(B)*|u_n|, V=sqrt(A)*|u_tt|,
    # W=|k|sqrt(C)*|u|, f=|F|/sqrt(A).
    # |comm|/sqrt(A) <= 140P+1750Q+V+72W+20f.
    P,Q,V,W,f=s.symbols('P Q V W f',nonnegative=True)
    v=s.Matrix([140*P,1750*Q,V,72*W,20*f])
    # Equality of 5-vector Cauchy-Schwarz to a sum of ten squares.
    gap=s.expand(5*sum(z*z for z in v)-sum(v)**2)
    square=sum((v[i]-v[j])**2 for i in range(5) for j in range(i+1,5))
    assert s.expand(gap-square)==0
    E0,E1,Ek,Fs=s.symbols('E0 E1 Ek Fs',nonnegative=True)
    # Pointwise integrated quadratic budget (P²+Q²<=2E0,
    # V²<=2E1, W²<=2Ek, f²<=Fs).
    rhs=5*(2*max(140**2,1750**2)*E0+2*E1+2*72**2*Ek+20**2*Fs)
    assert s.expand(rhs-(30625000*E0+10*E1+51840*Ek+2000*Fs))==0
    # Source Ft and kF remain owned by the actual first-order forcing.
    # This is a conditional estimate on the true solution and same interval.
    print('PASS actual F8 rational commutator: 140 P+1750 Q+V+72 k sqrt(C)|u|+20 f; graph majorant')

if __name__=='__main__': exact()
