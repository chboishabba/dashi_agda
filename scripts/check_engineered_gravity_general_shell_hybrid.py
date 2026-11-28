"""General fixed-parameter shell stability and hybrid passive-response bounds.
Conditional GR/EFT models; not localized engineered gravity.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    r,u,v,x,e=s.symbols('r u v x eta',positive=True)
    A=1-(1-v*v)*r*r
    B=1-2*x/r-(1-2*x-u*u)*r*r
    h=s.Function('h')(r)
    V=(A+B)/2-h*h/4-(A-B)**2/(4*h*h)
    sig=2*(v-u)
    p=(3*x+u*u-1)/u+(1-v*v)/v+u-v
    jet={h.subs(r,1):v-u,h.diff(r).subs(r,1):-(sig+2*p)/2,
         h.diff(r,2).subs(r,1):(1+2*e)*(sig+p)}
    eq(V.subs(r,1).subs(jet))
    eq(V.diff(r).subs(r,1).subs(jet))
    curv=s.factor(V.diff(r,2).subs(r,1).subs(jet))
    target=2*(-2*e*u**3*v**2-6*e*u**2*v**3*x+2*e*u**2*v**3-u**3+3*u**2*v**3*x+9*v**3*x**2-6*v**3*x+v**3)/(u*u*v*v*(u-v))
    eq(curv,target)
    base={u:s.Rational(1,2),v:s.Rational(3,4)}
    eq(curv.subs(base).subs(x,s.Rational(1,9)),-s.Rational(50,9))
    eq(curv.subs(base).subs(x,s.Rational(1,8)),e/2-s.Rational(325,72))
    eq(curv.subs(base).subs(x,s.Rational(19,144)),3*e/4-s.Rational(1159,288))
    # New rational example, positive pressure, static patch, strict DEC,
    # causal local slope. R0=1; external Lambda imposed, not localized.
    q={u:s.Rational(37,40),v:s.Rational(19,20),x:s.Rational(3,80),e:s.Rational(1,2)}
    eq(sig.subs(q),s.Rational(1,20))
    eq(p.subs(q),s.Rational(607,14060))
    assert 0<p.subs(q)<sig.subs(q)
    eq((1-3*x-u*u).subs(q),s.Rational(51,1600))
    eq(curv.subs(q),s.Rational(4957763,494209))
    assert curv.subs(q)>0
    # A locally linear barotropic EOS with eta=1/2 gives these jets;
    # radial stability only, not nonspherical or microscopic stability.
    # Hybrid: relaxing a passive positive-energy internal mode always
    # subtracts from bare static radial stiffness. Need direct stiffness.
    a,b,c,d,y,z=s.symbols('a b c d y z',real=True)
    E=(a+d)*y*y/2+c*y*z+b*z*z/2
    eq(E,b*(z+c*y/b)**2/2+(a+d-c*c/b)*y*y/2)
    eq(E.subs(z,-c*y/b),(a+d-c*c/b)*y*y/2)
    # For b>0, bare a<0, direct positive d must exceed -a+c²/b.
    # Source/receiver inverse in any positive Hessian, work retained.
    S,J=s.symbols('S J',real=True)
    H=s.Matrix([[a+d,c],[c,b]])
    F=s.Matrix([S,J])
    qstar=H.inv()*F
    assert (H*qstar-F).applyfunc(s.simplify)==s.zeros(2,1)
    eq((qstar.T*H*qstar)[0]/2,(F.T*qstar)[0]/2)
    print('PASS general shell curvature, three legacy families, stable rational shell, hybrid Schur and work')
    print('OPEN actual localized vacuum, microscopic EOS, nonspherical stability, tensor shielding and continuum F8')

if __name__=='__main__':main()
