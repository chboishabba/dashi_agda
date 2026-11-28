"""BR281 rational constant replay for the uniform analytic G3 proof.
Checks quantitative inequalities, NOT the CK theorem or a native proof.
"""
from fractions import Fraction as F
import sympy as s


def main():
    # Original P0T radial potential and Newton norm.
    eps=F(1,4);q=F(8,9)*eps**2;qt=F(4,3)**4*q
    assert q==F(1,18) and qt==F(128,729) and qt<F(1,2)
    upper=1/(1-qt);lower=1-qt/(1-qt)
    assert upper<2 and lower>F(1,2)
    # |Im z|<=1/2, Re(1+z.z)>=3/4(1+|Re z|²),
    # numerator of each a_i <=4(1+|Re z|²).
    a=2*eps*4*F(4,3)**2;assert a<4
    seed=max(1+3*a*a+a,1+3*a,1+3*a*a+3*a)
    assert seed<64 and seed*upper**2<256 and seed/lower**2<256
    # Polydisk radius 1/4 about any real centre lies in tube.
    assert 3*F(1,4)**2<F(1,2)**2
    # Cauchy on radius 1/8, initial harmonic shift first jets.
    dg=256*8;shift=16*256*F(3,2)*dg
    U0=2**25;dU0=16*U0;assert max(dg,shift)<U0
    eta=F(1,2**24);rho=F(1,32);n=90
    inv=256/(1-256*5*eta)
    assert inv<512 and 256*5*eta*inv<F(1,2)
    D=2**26;gi=512;dgi=25*gi*gi*D
    Gamma=F(15,2)*gi*D;dGamma=F(15,2)*dgi*D
    dC=25*dgi*F(3,2)*D;covC=5*Gamma*25*gi*F(3,2)*D
    lowerQ=10*dGamma+50*Gamma**2+dC+covC
    coeff=4*gi+1;source=4*lowerQ+D+3*n*coeff*dU0
    c=2**128;assert max(coeff,source)<c
    A=n*(3/rho+1/eta);T=F(3,32)/(A*c);w=1/(4*A)
    assert w<eta and F(1,2)*w-A*w*w/2-c*T==0
    # The scalar positive-coefficient implicit majorant obeys the
    # quasilinear majorant equation exactly (original P0V form).
    z,t,W,r,e,N,C=s.symbols('z t W r e N C',positive=True)
    P=(1-z/r)*W-N*(3/r+1/e)*W**2/2-C*t
    wt=-s.diff(P,t)/s.diff(P,W);wz=-s.diff(P,z)/s.diff(P,W)
    assert s.cancel(wt*(1-z/r-N*W/e)-C*(1+3*N*wz))==0
    print('BR281 tube contraction',qt,'psi lower/upper',lower,upper,'metric cap',256,'time bound',T,flush=True)
    print('BR281 uniform analytic coefficient and implicit majorant inequalities PASS; classical CK and constraint propagation proof separate',flush=True)

if __name__=='__main__':main()
