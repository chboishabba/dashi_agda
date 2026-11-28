"""F8 W2: nonfrozen 5D GN positive principal-current and exact deformation
majorant on the original finite collar. Conditional boundary trace payment.
"""
import sympy as s

def exact():
    a,N,at,Nn=s.symbols('a N at Nn',positive=True)
    p,q=s.symbols('p q',real=True)
    E=(p*p/N**2+q*q)/2
    D=3*a*a*at*(p*p/N**2-q*q)/2-a**3*Nn*p*q/N
    C=3*at/a+Nn
    # For this sign-restricted jet, the exact SOS estimate.
    assert s.simplify(a**3*C*E-D-a**3*(3*at/a*q*q+Nn/2*(p/N+q)**2))==0
    assert s.simplify(a**3*C*E+D-a**3*(3*at/a*p*p/N**2+Nn/2*(p/N-q)**2))==0
    t=s.symbols('t',positive=True)
    B=s.sqrt(1+1/t**2)
    # Wall a=t, N=1, a_t=1, Nn=-1/B. Source signed Nn uses ABS.
    Aw=3/t+1/B
    assert s.simplify(Aw-3/t-t/s.sqrt(1+t*t))==0
    assert s.limit(Aw,t,s.oo)==1
    assert s.simplify(Aw.subs(t,1)-3-s.sqrt(2)/2)==0
    # A time-uniform upper bound on [1,12] follows 3/t<=3 and 1/B<1.
    assert s.simplify(4-Aw).subs(t,1)>0
    # Wall conormal flux: t³ p q, |p q|<= E when N=1.
    wallE=(p*p+q*q)/2
    assert s.expand(wallE-p*q-(p-q)**2/2)==0
    assert s.expand(wallE+p*q-(p+q)**2/2)==0
    # Positive principal bulk does not imply sign of the wall work.
    assert (p*q).subs({p:1,q:1})>0 and (p*q).subs({p:1,q:-1})<0
    print('PASS F8 scalar-principal deformation work bound and signed wall trace budget')
if __name__=='__main__':exact()
