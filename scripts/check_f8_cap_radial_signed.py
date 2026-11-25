"""Original axial TT receiver, exact radial BIDI derivative transport and cap signs."""
import json
from fractions import Fraction as Q
import sympy as S
from check_f8_cap_diamond_green import geometry, coeff

def run():
    geom=geometry();r=S.symbols('r',positive=True);f=S.Function('f')(r);w=S.Function('w')(r)
    J=lambda a:S.diff(a,r)/r;lap=lambda a:S.diff(a,r,2)+2*S.diff(a,r)/r
    T=lambda a:S.Rational(2,5)*lap(lap(a))+S.Rational(4,7)*r*r*J(J(lap(a)))+S.Rational(1,35)*r**4*J(J(J(J(a))))
    C=[3/r**5,-3/r**4,3/r**3,-2/r**2,1/r];D=lambda a:sum(c*S.diff(a,r,j) for j,c in enumerate(C))
    assert S.expand(T(w/r)-D(w))==0
    assert S.simplify(lap(w/r)-S.diff(w,r,2)/r)==0
    assert S.expand(T(lap(w/r))-D(S.diff(w,r,2)))==0
    t,z=S.symbols('t z',positive=True);U=S.Function('U')(t,z,r);v=S.Function('v')(t)
    L=lambda a:-S.diff(a,t,2)+S.diff(a,z,2)-3/z*S.diff(a,z)+S.diff(a,r,2)
    B=lambda a:S.diff(a,z)+v*S.diff(a,t)
    for j in range(7):
        assert S.expand(L(S.diff(U,r,j))-S.diff(L(U),r,j))==0
        assert S.expand(B(S.diff(U,r,j))-S.diff(B(U),r,j))==0
    # Shifted-coefficient positivity on u=r/eps >=.99, X>=50.
    X,Y=S.symbols('X Y');P=S.Integer(1);p=1;rows=[]
    assert Q(396,10000)/Q(1,25)==Q(99,100)
    assert 1/(1-Q(99,100)**2)>50
    for j in range(7):
        poly=S.Poly(S.expand((-1)**j*P.subs(X,Y+50)),Y)
        assert all(x>0 for x in poly.all_coeffs())
        rows.append(dict(order=j,parity=p,degree=poly.degree(),constant=str(poly.all_coeffs()[-1]),minimum_coefficient=str(min(poly.all_coeffs()))))
        P=S.expand(P+2*(X*X-X)*(S.diff(P,X)-P) if p else 2*X*X*(S.diff(P,X)-P));p=1-p
    # Receiver window coefficient signs for the original two rows.
    b=S.symbols('b',positive=True);beta=S.sqrt(1+b*b);dt=lambda a:S.diff(a,b)*(-b/beta)
    A=b*b*(1+b*b);B0=-b**4/beta;B2=B0+2*b*b*beta
    assert S.simplify(B0-2*dt(A)-(4*b*b+7*b**4)/beta)==0
    assert S.simplify(dt(B0)-dt(dt(A))+(4*b*b+14*b**4+9*b**6)/(1+b*b)**2)==0
    assert S.simplify(dt(B2)-dt(B0)+4*b*b+2*b**4/(1+b*b))==0
    # chi' < 0 and chi'' > 0 for positive cap u>=.99,X>=50.
    assert 4*Q(99,100)**2*50*(50-2)>2
    assert 1-10*Q(7,20000)>Q(99,100)
    # G in 1 transverse + 1 normal spatial dimensions has positive integrable
    # density on q>0, eta<=1/16, but moving-wall inverse not yet sign-certified.
    assert coeff(1)==Q(-15,2) and coeff(2)>0
    lower=1+coeff(1)*Q(1,16);assert lower==Q(17,32)
    upper=1+coeff(2)*Q(1,16)**2/(1-Q(1,16));assert upper<Q(33,32)
    return dict(geometry=geom,axial_tt_coefficients=[str(c) for c in C],commutation_orders=7,radial_derivative_signs=rows,receiver_p_sign='strictly negative in interior cap for both E4 and SMS',a0_signs={'E4':'negative','SMS':'positive'},free_green_factor_bounds=[str(lower),str(upper)],scope='original radial full-line derivative transport; negative image causally excluded, direct kernel factor sign only; no boundary-to-boundary positivity or signed receiver interval')
if __name__=='__main__':print(json.dumps(run(),indent=2))
