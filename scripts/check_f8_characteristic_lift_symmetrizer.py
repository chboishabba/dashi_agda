"""F8 original-characteristic boundary lift and positive k-weighted symmetrizer.

Original incoming L-R=q(t), q=12 Pi; chi(n)=1-2n.
Replace L by ell=L-q chi. Then ell=R at the inner wall and R=0
at the outer wall. The characteristic energy has zero left flux and
nonpositive right flux without independent boundary trace assumptions.
Weight 1+2 k²/a² exactly cancels the bulk k² H(R+ell) coupling.

Algebraic identity on the original GN geometry; independent source,
coefficient, time-commutator, and continuum estimates remain open.
"""
import sympy as s


def exact():
    H,R,ell,q,qd,chi,chin,rn,ln=s.symbols(
        'H R ell q qd chi chin rn ln',real=True)
    a,c,N,Nn,k=s.symbols('a c N Nn k',positive=True)
    L=ell+q*chi
    W=(R+L)/2
    V=(R-L)/2
    src=(Nn-3*N*c/a)*V-3*N/a*W-N*k*k*H/a**2
    SR=src+Nn*W;SL=src-Nn*W
    Ht=N*W;Rt=N*rn+SR
    ellt=-N*ln+SL-qd*chi-N*q*chin
    assert s.simplify(ellt+qd*chi+N*(ln+q*chin)-SL)==0
    weight=1+2*k*k/a**2
    wt=-4*k*k*N/a**3  # actual GN a_t=N
    Edot=wt*H*H/2+weight*H*Ht+R*Rt+ell*ellt
    flux=N*(R*R-ell*ell)/2
    # d_n flux=N_n(R²-ell²)/2+N(R R_n-ell ell_n).
    density=s.expand(Edot-N*(R*rn-ell*ln)-Nn*(R*R-ell*ell)/2)
    assert not density.has(rn,ln)
    assert s.simplify(s.diff(density,H,R)-N/2)==0
    assert s.simplify(s.diff(density,H,ell)-N/2)==0
    assert s.simplify(s.expand(s.diff(density,H,q)).coeff(k,2)-N*chi/a**2)==0
    assert s.simplify(s.expand(s.diff(density,H,2)).coeff(k,2)+4*N/a**3)==0
    n=s.symbols('n',real=True)
    cutoff=1-2*n
    assert cutoff.subs(n,0)==1 and cutoff.subs(n,s.Rational(1,2))==0
    assert s.simplify(flux.subs(ell,R))==0
    assert s.simplify(flux.subs(R,0)+N*ell*ell/2)==0
    assert weight.subs(k,0)==1
    print('PASS original incoming-source lift, homogeneous/dissipative boundaries and exact k² symmetrizer cancellation')

if __name__=='__main__':exact()
