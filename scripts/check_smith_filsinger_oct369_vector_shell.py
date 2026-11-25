"""Consume original OCT369 signed cube for vector shell angular projection.
Run with a local copy of the pinned master OCT369 preflight as argv[1].
Classical Lebedev, VSH and radial Poynting identities; no physical calibration.
"""
import hashlib,json,runpy,sys
from pathlib import Path
from itertools import product
import sympy as s
raw=Path(sys.argv[1]).read_bytes()
blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
assert blob=='1f493bdedf3ca058470db4fe0154c13d4df905b4'
d=runpy.run_path(sys.argv[1]);sites=sorted(d['punctured27']);origin=d['origin']
weights={1:s.Rational(1,21),2:s.Rational(4,105),3:s.Rational(9,280)}
pts=[(s.Matrix(p)/s.sqrt(sum(i*i for i in p)),weights[sum(i!=0 for i in p)]) for p in sites]
x,y,z=s.symbols('x y z',real=True);n=s.Matrix([x,y,z]);checks=[]
def eq(name,a,b):
    delta=a-b
    assert all(s.simplify(t)==0 for t in delta) if isinstance(delta,s.MatrixBase) else s.simplify(delta)==0,name
    checks.append(name)
def moment(k):
    if any(i%2 for i in k):return s.Integer(0)
    return s.prod(s.factorial2(i-1) for i in k)/s.factorial2(sum(k)+1)
def avg(a):return s.expand(sum(c*moment(k) for k,c in s.Poly(s.expand(a),x,y,z).terms()))
def project(a):return 3*n.applyfunc(lambda t:avg(t*a))
for k in product(range(8),repeat=3):
    if sum(k)<=7:eq('moment_'+str(k),sum(w*s.prod(v[i]**k[i] for i in range(3)) for v,w in pts),moment(k))
assert len(checks)==120
alias=sum(w*v[0]**8 for v,w in pts)-s.Rational(1,9)
assert alias!=0
p=s.Matrix(s.symbols('p:3',real=True));b=s.Matrix(s.symbols('b:3',real=True));a,d,e,f,g=s.symbols('a d e f g',real=True)
Q=s.Matrix([[a,d,e],[d,f,g],[e,g,-a-f]])
P=lambda v:v-n*n.dot(v)
T=lambda v:n.cross(v)
# Tangential l=1 and l=2 (half of gradient for l=2).
P1=P(p);T1=T(p);P2=P(Q*n);T2=T(Q*n)
eq('poloidal_tangential',avg(n.dot(P1)**2),0)
eq('toroidal_tangential',n.dot(T2),0)
eq('dipole_poloidal_square_null',project(P1.dot(P1)),s.zeros(3,1))
eq('dipole_toroidal_square_null',project(T1.dot(T1)),s.zeros(3,1))
eq('same_family_P_mixed',project((P1+P2).dot(P1+P2)),s.Rational(6,5)*Q*p)
eq('same_family_T_mixed',project((T1+T2).dot(T1+T2)),s.Rational(6,5)*Q*p)
eq('cross_family_12_null',project(P1.dot(T2)),s.zeros(3,1))
eq('cross_family_11_nonzero',project((P1+T(b)).dot(P1+T(b))),2*b.cross(p))
eq('dipole_poloidal_norm',avg(P1.dot(P1)),s.Rational(2,3)*p.dot(p))
eq('dipole_toroidal_norm',avg(T(b).dot(T(b))),s.Rational(2,3)*b.dot(b))
eq('cross_family_norm_orthogonal',avg(P1.dot(T(b))),0)
eq('quadrupole_tangent_norm',avg(P2.dot(P2)),s.trace(Q*Q)/5)
Pz=s.symbols('Pz',positive=True);tx,ty,bz=s.symbols('tx ty bz',real=True);pv=s.Matrix([0,0,Pz]);target=s.Matrix([tx,ty,0]);bv=pv.cross(target)/(2*Pz**2)+s.Matrix([0,0,bz])
eq('BIDI cross family reverse',2*bv.cross(pv),target)
eq('cross family norm residual',bv.dot(bv),(tx*tx+ty*ty)/(4*Pz**2)+bz*bz)
# Original full-vector Poynting boundary: homogeneous isotropic TE radial shell,
# RMS exp(i omega t), E=(u/r) Phi_lm, H=(L u/r^2 Y n+u'/r Psi)/(i omega mu).
# L=l(l+1), integral |Y|^2 over sphere = 4 pi. Radial u''=(L/r²-k²)u.
r,omega,mu,eps,sigma,L=s.symbols('r omega mu eps sigma L',positive=True)
U,V,Up,Vp=s.symbols('U V Up Vp',real=True)
K=L/r**2-omega**2*mu*eps
Upp=K*U-omega*mu*sigma*V;Vpp=K*V+omega*mu*sigma*U
flux=-4*s.pi*L*(U*Vp-V*Up)/(omega*mu)
Dflux=sum(s.diff(flux,a)*b for a,b in zip((U,V,Up,Vp),(Up,Vp,Upp,Vpp)))
eq('TE radial signed Poynting',Dflux,-4*s.pi*L*sigma*(U*U+V*V))
# Across a no-sheet interface u and u'/mu are continuous (same omega).
m1,m2=s.symbols('m1 m2',positive=True)
eq('TE interface work continuity',flux.subs(mu,m1),flux.subs({mu:m2,Up:Up*m2/m1,Vp:Vp*m2/m1}))
print(json.dumps({'status':'CONDITIONAL_OCT369_VECTOR_ANGULAR_AND_TE_RADIAL','donor_blob':blob,'checks':len(checks),'moments':120,'other_checks':checks[120:],'degree8_alias':str(alias),'zero_site':list(origin),'scope':'Exact angular quadrature and scalar energy-density projection of vector harmonics, plus homogeneous isotropic TE radial flux identity. No TM stratified solution, calibrated source or HF constitutive law. No physical extraction.'},indent=2))
