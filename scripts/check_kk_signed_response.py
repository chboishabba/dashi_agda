import sympy as s
import numpy as np
f=s.Rational(1,4)
z=s.symbols('z')
R=1-f+f/(1+z)
assert s.solve(R-2,z)==[-s.Rational(4,5)]
assert s.solve(R,z)==[-s.Rational(4,3)]
# two distinct source/probe vectors; positive static kernel can have negative cross response
# baseline metric contribution held fixed; scalar response from cross channel
K=s.Matrix([[1,s.Rational(3,4)],[s.Rational(3,4),1]])
u=s.Matrix([1,0]); v=s.Matrix([0,1]); C=K.inv()
assert K.is_positive_definite
print('kernel',K,'inverse',C,'cross', (v.T*C*u)[0], 'self',(u.T*C*u)[0])
# paired target: direct source in channel 1, probe in channel 2
# K=[[1,r],[r,1]], cross=-r/(1-r²)
for target in [-3,5]:
 r=(-2*target)/(1+np.sqrt(1+4*target**2))
 k=np.array([[1,r],[r,1]])
 cross=np.linalg.inv(k)[1,0]
 assert np.isclose(cross,target) and min(np.linalg.eigvalsh(k))>0
 print('target',target,'r',r,'eigenvalues',np.linalg.eigvalsh(k),'total',.75+.25*cross)
# dispersive scalar response, positive oscillator stiffness, stable coupled system
A=1.; mu=4.; lam=1.;
for w in [0,.5,1.5,2.1]:
 eff=A-w*w-lam*lam/(mu-w*w)
 print('omega',w,'effective inverse',eff,'response',1/eff)
assert A*mu>lam*lam
# universal source/probe aligned: positive quadratic form cannot reverse sign
x,y=s.symbols('x y',real=True)
assert s.expand((s.Matrix([x,y]).T*C*s.Matrix([x,y]))[0]-((x+y)**2*s.Rational(2,7)+(x-y)**2*2))==0
print('PASS inverse endpoints, stable cross response, aligned positivity, dispersion')
