"""F8 W3 critical negative control: reciprocal wave inverses alone
are NOT an energy estimate. Original wall loop H7 -> N2_5 -> H7
has exact gain one. No fabricated simultaneous closure.
"""
import sympy as s
from check_f8_characteristic_jet_reverse import reconstruct,coefficients
from check_f8_wall_elliptic_jet_weld import inverse

def exact():
    t0=s.Integer(1);k=s.Rational(5,2);t=s.symbols('t',positive=True)
    A,B,C,D=coefficients(t,k,6)
    old=tuple([[s.simplify(x.subs(t,t0)) for x in seq] for seq in (A,B,C,D)])
    g=s.sqrt(1+t*t)
    functions={'A':t**3,'B':t**3,'C':t*k*k,'At':3*t*t,
        'Bn':-t**4/g-3*t*t*g,'An':t**4/g-3*t*t*g,
        'Atn':s.diff(t**4/g-3*t*t*g,t),
        'Bnn':16*t**3+6*t,'Cn':-k*k*(t*t/g+g)}
    coeff={name:[s.simplify(s.diff(v,t,j).subs(t,t0)) for j in range(6)]
           for name,v in functions.items()}
    h7=s.symbols('h7',real=True)
    H=[s.Integer(0)]*7+[h7]
    N1=[s.Integer(0)]*8
    F=[s.Integer(0)]*6;Fn=[s.Integer(0)]*6
    normal2,normal3=inverse(H,N1,F,Fn,coeff)
    assert s.simplify(normal2[5]-h7)==0
    back=reconstruct(H[0],H[1],N1[:6],normal2,F,old,7)
    assert s.simplify(back[7]-h7)==0
    x=s.symbols('x')
    assert s.diff(normal2[5].subs(h7,x),x)==1
    assert s.diff(back[7].subs(h7,x),x)==1
    assert coeff['A'][0]==coeff['B'][0]==1
    print('PASS F8 critical negative control: H7 -> N2_5 -> H7 has exact gain 1')
    print('Need an independent higher time/normal graph estimate, not reciprocal substitution')

if __name__=='__main__':exact()
