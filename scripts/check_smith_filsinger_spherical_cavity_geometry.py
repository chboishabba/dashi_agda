"""MR30-39 spherical scalar thin-shell Galerkin geometry; not vector Maxwell or calibrated source."""
import sympy as s
import json, math
x,y,z=s.symbols('x y z',real=True); n=s.Matrix([x,y,z]); checks=[]
def avg(expr):
    out=0
    for powers,c in s.Poly(s.expand(expr),x,y,z).terms():
        if any(k%2 for k in powers):continue
        out+=c*s.prod(s.factorial2(k-1) for k in powers)/s.factorial2(sum(powers)+1)
    return s.expand(out)
def eq(name,a,b):
    d=a-b
    assert all(s.simplify(t)==0 for t in d) if isinstance(d,s.MatrixBase) else s.simplify(d)==0,(name,d)
    checks.append(name)
p=s.Matrix(s.symbols('p:3',real=True));b=s.Matrix(s.symbols('b:3',real=True));a,d,e,f,g=s.symbols('a d e f g',real=True)
Q=s.Matrix([[a,d,e],[d,f,g],[e,g,-a-f]])
u=p.dot(n); v=n.dot(Q*n); w=b.dot(n); proj=lambda h:3*n.applyfunc(lambda ni:avg(ni*h))
eq('constant norm',avg(1),s.Integer(1))
eq('dipole squared has no dipole',proj(u*u),s.zeros(3,1))
eq('quadrupole squared has no dipole',proj(v*v),s.zeros(3,1))
eq('mixed parity dipole projection',proj((u+v)**2),s.Rational(4,5)*Q*p)
eq('odd background dipole projection',proj(w*u*u),(p.dot(p)*b+2*p.dot(b)*p)/5)
c0=s.symbols('c0',real=True)
eq('zero mode mixed dipole projection',proj((c0+u+v)**2),2*c0*p+s.Rational(4,5)*Q*p)
eq('mean square norm',avg((u+v)**2),p.dot(p)/3+s.Rational(2,15)*s.trace(Q*Q))
eq('odd-even orthogonality',avg(u*v),0)
eq('quadratic zero mode retained',avg(u*u),p.dot(p)/3)
# Reverse solve Qp for p aligned with z; target components in same frame.
P=s.symbols('P',positive=True); tx,ty,tz=s.symbols('tx ty tz',real=True); t=s.Matrix([tx,ty,tz]); scale=5/(4*P)
Qmin=scale*s.Matrix([[-tz/2,0,tx],[0,-tz/2,ty],[tx,ty,tz]])
eq('reverse exact target',s.Rational(4,5)*Qmin*s.Matrix([0,0,P]),t)
eq('minimum norm cost',s.trace(Qmin*Qmin),scale**2*(2*tx**2+2*ty**2+s.Rational(3,2)*tz**2))
# Residual space preserving target and tracelessness: traceless xy block.
r,k=s.symbols('r k',real=True);N=s.Matrix([[r,k,0],[k,-r,0],[0,0,0]])
eq('reverse null',N*s.Matrix([0,0,P]),s.zeros(3,1))
eq('reverse minimum orthogonality',s.trace(Qmin*N),0)
eq('reverse residual norm',s.trace((Qmin+N)**2),s.trace(Qmin**2)+2*(r*r+k*k))
# same-axis mixed example optimal energy partition, amplitude target along z.
T=s.symbols('T',positive=True); Qz=Qmin.subs({tx:0,ty:0,tz:T})
E=s.simplify(P**2/3+s.Rational(2,15)*s.trace(Qz*Qz))
eq('aligned reverse energy',E,P**2/3+5*T*T/(16*P**2))
# AM-GM equality at P^4=15 T²/16; target/mean-square limit 2 sqrt(15)/5.
eq('aligned minimum energy',E.subs(P**2,s.sqrt(15)*T/4),s.sqrt(15)*T/6)
# Source shape: equal antipodal axisymmetric caps cancel l=1, opposed caps add.
mu=s.symbols('mu',real=True); c=s.symbols('c',real=True)
north=s.integrate(mu,(mu,c,1))/2;south=s.integrate(mu,(mu,-1,-c))/2
eq('equal cap dipole null',north+south,0)
eq('opposed cap dipole nonzero',3*(north-south),3*(1-c*c)/2)
# Frequency reference: radial scalar shell l>=1, l=0 kept separately (not propagating Schumann).
# Same force amplitude and same fixed damping; compare velocity response at off-band and resonance.
f0=7.83;Qf=5.; Rearth=6371000.; light=299792458.; fs=.005
speed=2*math.pi*Rearth*f0/math.sqrt(2)
ratio=fs/f0; velocity_ratio=(ratio/Qf)/math.sqrt((1-ratio**2)**2+(ratio/Qf)**2)
# normalized temporal doubling: cos² factor 1/2 for oscillatory coefficient, DC same.
# No physical excitation, source spectrum, material coefficient or conversion assumed.
result={'status':'CONDITIONAL_SPHERICAL_SCALAR_GEOMETRY','checks':checks,'count':len(checks),'fitted_effective_speed_over_c':speed/light,'ideal_f1_Hz':light*math.sqrt(2)/(2*math.pi*Rearth),'nondispersive_calibrated_modes_Hz':[f0*math.sqrt(l*(l+1)/2) for l in range(1,6)],'equal_force_5mHz_velocity_ratio':velocity_ratio,'equal_force_5mHz_load_ratio':velocity_ratio**2,'scope':'Scalar angular modes, normalized sphere measure. No actual vector Maxwell/radial boundary, HF mode or physical source calibration; equal force diagnostic only; no atmospheric excitation settings.'}
print(json.dumps(result,indent=2))
