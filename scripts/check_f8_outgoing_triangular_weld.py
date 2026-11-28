"""F8 noncircular outgoing high-time boundary closure.

Differentiated R=0 condition solves all lower normal jets in terms of
lower tangential-time jets. For m<=6, the outgoing energy flux is negative
apart from a source norm controlled by time levels E0..Em, not by a
separate normal graph H_nn or an H_(m+1) boundary trace.
"""
from math import comb
import sympy as s


def normal_from_time(N, H, order):
    """N_j=d_t^j N(t,L), H_j=d_t^j H(t,L); return n_j=d_t^j H_n."""
    if len(N)<order+1 or len(H)<order+2 or N[0]==0:
        raise ValueError('missing outgoing jets or positive lapse')
    normals=[]
    for m in range(order+1):
        z=-H[m+1]-sum(comb(m,j)*N[j]*normals[m-j] for j in range(1,m+1))
        normals.append(s.factor(z/N[0]))
    return normals


def outgoing_defects(N,H,order):
    normal=normal_from_time(N,H,order-1)
    return [s.factor(-sum(comb(m,j)*N[j]*normal[m-j] for j in range(1,m+1)))
            for m in range(1,order+1)]


def exact():
    N=list(s.symbols('N0:7',real=True,nonzero=True))
    H=list(s.symbols('h0:8',real=True))
    normal=normal_from_time(N,H,5)
    for r in range(6):
        assert s.factor(H[r+1]+sum(comb(r,j)*N[j]*normal[r-j] for j in range(r+1)))==0
    defects=outgoing_defects(N,H,6)
    assert all(not x.has(H[7]) for x in defects)
    assert s.simplify(defects[0]-N[1]*H[1]/N[0])==0
    for m,g in enumerate(defects,1):
        assert all(not g.has(H[j]) for j in (0,*range(m+1,8)))
        assert s.simplify(g.subs(dict.fromkeys(H,0)))==0
    # Exact original F8 outer-wall lapse, uniformly positive on 1<=t<=12.
    t=s.symbols('t',positive=True)
    Nphys=s.cosh(s.Rational(1,2))-t*s.sinh(s.Rational(1,2))/s.sqrt(1+t*t)
    assert s.simplify(Nphys-s.expand_trig(s.cosh(s.asinh(t)-s.Rational(1,2)))/s.sqrt(1+t*t))==0
    for ti in (s.Integer(1),s.Rational(21,20),s.Integer(12)):
        assert float(Nphys.subs(t,ti))>0.6
    B,b,q,g=s.symbols('B b q g',positive=True)
    assert s.simplify(B*(g-b*q)*q+B*b*(q-g/(2*b))**2-B*g*g/(4*b))==0
    print('PASS original F8 outer R=0 triangular elimination m1..6; no independent lower normal trace or H7 wall trace')

if __name__=='__main__':exact()
