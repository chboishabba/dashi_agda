"""Exact local constitutive work and finite endpoint reconstruction.
Normalized material fixture only; no environmental excitation model.
Donor: check_smith_filsinger_dispersive_finite_line.py at 116cd7de.
"""
import sympy as s

def gradient(p0,p1,a0,a1,beta):
    return (a0+a1)*(p0+p1)/4+beta*(p0+p1)*(p0*p0+p1*p1)/4

def storage(p,a,beta):
    return a*p*p/2+beta*p**4/4

def step_receipt(p0,p1,a0,a1,beta,eta,h):
    # Manufactured endpoint pair; reconstruct the required local voltage.
    rate=(p1-p0)/h
    v=eta*rate+gradient(p0,p1,a0,a1,beta)
    mod=(a1-a0)*(p0*p0+p1*p1)/4
    loss=h*eta*rate**2
    work=v*(p1-p0)
    delta=storage(p1,a1,beta)-storage(p0,a0,beta)
    return v,delta,work,loss,mod

def run():
    p,q,a,b,k,e,h=s.symbols('p q a b k e h', real=True)
    v,du,w,l,m=step_receipt(p,q,a,b,k,e,h)
    checks=[s.cancel(du-w+l-m)==0,
            s.simplify(gradient(p,p,a,a,k)-(a*p+k*p**3))==0,
            s.simplify(m.subs(b,a))==0,
            s.simplify(l.subs(q,p))==0,
            s.simplify(du.subs({q:p,b:a}))==0]
    R=s.Rational
    for endpoints in [(R(1,3),R(2,3)),(R(2,3),R(-1,3)),(R(0),R(0))]:
        for a0,a1 in [(R(2),R(3)),(R(3),R(2)),(R(2),R(2))]:
            v,du,w,l,m=step_receipt(*endpoints,a0,a1,R(1,2),R(1,3),R(1,5))
            checks += [du-w+l-m==0,l>=0]
    assert all(checks),checks
    print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
if __name__=='__main__':run()
