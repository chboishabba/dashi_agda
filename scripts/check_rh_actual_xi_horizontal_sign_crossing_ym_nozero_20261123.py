#!/usr/bin/env python3
"""High-precision ACTUAL completed xi horizontal reflection, with controls.

Actual mpmath zetazero ordinates are numerical, not certified interval proofs.
The finite reflection-pair and post-sixth arithmetic is exact via SymPy.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps=85
xi=lambda s: s*(s-1)/2*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
def test(t,label,zero):
    s=mp.mpf('.5')+1j*t
    center=xi(s);der=mp.diff(xi,s)
    assert abs(mp.re(der))<mp.mpf('1e-46')
    assert abs(mp.im(der))>mp.mpf('1e-10')
    if zero:assert abs(center)<mp.mpf('1e-55')
    else:
        assert abs(center)>mp.mpf('1e-10')
        assert abs(mp.im(center))<mp.mpf('1e-55')
    for h in map(mp.mpf,('.001','.000001','.00000001')):
        p=xi(s+h);m=xi(s-h)
        assert abs(m-mp.conj(p))<mp.mpf('1e-48')
        assert abs(mp.im(p)+mp.im(m))<mp.mpf('1e-48')
        assert abs(mp.im((p-m)/(2*h)-der))<abs(mp.im(der))/500
        if zero:
            assert abs(h*mp.diff(xi,s+h)/p-1)<mp.mpf('.002')
    print(label,'t=',mp.nstr(t,23),'xi=',mp.nstr(center,14),
          'xi_horizontal_derivative=',mp.nstr(der,20))
    return der
d1=test(mp.im(mp.zetazero(1)),'actual zero 1',True)
d2=test(mp.im(mp.zetazero(2)),'actual zero 2',True)
d3=test(mp.mpf(20),'NONZERO height 20',False)
assert mp.im(d1)>0 and mp.im(d2)<0 and mp.im(d3)<0
print('PASS imaginary horizontal sign crossing DOES NOT imply xi zero')

w,a=sp.symbols('w a',real=True,nonzero=True)
D=sp.cancel(1/(w-a)+1/(w+a))
assert sp.simplify(D-2*w/(w*w-a*a))==0
assert D.subs(w,0)==0 and sp.simplify(sp.diff(D,w).subs(w,0)+2/a**2)==0
assert sp.simplify(sp.limit(D,a,0)-2/w)==0
print('PASS selected reflected-pole midpoint cancellation is NOT a xi zero')

z=sp.symbols('z');g=sp.Integer(2);A=sp.Rational(1,3)
P=sp.expand((z*z+g*g)*((z-sp.I*g)**2-A*A)*((z+sp.I*g)**2-A*A))
assert sp.simplify(P.subs(z,-z)-P)==0
assert all(sp.im(c)==0 for c in sp.Poly(P,z).all_coeffs())
assert all(sp.simplify(P.subs(z,r))==0 for r in
           (sp.I*g,-sp.I*g,A+sp.I*g,-A+sp.I*g,A-sp.I*g,-A-sp.I*g))
assert sp.simplify(sp.diff(P,z).subs(z,sp.I*g)-sp.I*sp.Rational(580,81))==0
print('PASS functional reflection and simple critical signed jet coexist with off-line zeros')

d,sigma,excess=sp.symbols('d sigma excess',nonnegative=True)
I=sp.symbols('I')
Dtotal=2*d+excess
H=2*Dtotal+I
assert sp.simplify(H+sigma-(4*d+I)-(2*excess+sigma))==0
print('PASS signed RH terminal gap >= 0 under already-owned H-I=2D, D>=2d, S>=0')
print('OPEN actual global RH exclusion, and physical original YM CMP119/W3/OS same-H')

# A simple complex xi zero is a local 2D oriented winding, NOT two zeros.
# Nonzero imaginary-part crossings need not enclose any xi zero.
for label,t,want in [('zero1',mp.im(mp.zetazero(1)),1),
                     ('zero2',mp.im(mp.zetazero(2)),1),
                     ('nonzero20',mp.mpf(20),0)]:
    c=mp.mpf('.5')+1j*t
    radius=mp.mpf('.0003')
    vals=[xi(c+radius*mp.exp(2j*mp.pi*k/128)) for k in range(129)]
    assert min(abs(v) for v in vals)>mp.mpf('1e-12')
    winding=sum(mp.arg(vals[k+1]/vals[k]) for k in range(128))/(2*mp.pi)
    assert abs(winding-want)<mp.mpf('1e-24')
    jacobian=abs(mp.diff(xi,c))**2
    assert jacobian>0
    print('NUMERIC COMPLEX winding',label, 'w=',mp.nstr(winding,7),
          'Jacobian=',mp.nstr(jacobian,18))
print('PASS: complex-zero winding distinguishes actual simple zero from imaginary-only crossing')
