"""Exact restored-periodic Maxwell/Lorentz selective load, 4-bin source.

Finite synthetic fixture only: no calibrated physical receiver or CI.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator,energy
q=S.Rational
D=q(1,10); Z=q(1,200);G=q(204); amp=S.sqrt(q(1,300))
A,B,M=generator(n=2,load_conductance=1/Z)
A=S.Matrix(A);A[1,1]-=G/q(2)
K=(S.eye(8)-D*A/2).inv();T=2*K-S.eye(8)
# energy strict decay: each step U1-U0 = -dt (sigma ||E_mid||² + G E1mid² + Y ||E_mid||² + gamma/alpha ||V_mid||²)
# constant state linear propagator T; mid K z (source=0). Observability: D K T^k full column rank
J=S.Matrix([[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1]])
rank=S.Matrix.vstack(*[J*K*T**i for i in range(2)]).rank()
print('rank',rank,flush=True)
assert rank==8
P=((0,0),(1,0),(0,1),(0,0))
kicks=[D*K*B*(2*amp*S.Matrix(pair)/Z) for pair in P]
v=S.zeros(8,1)
for kick in kicks:v=T*v+kick
z0=(S.eye(8)-T**4).inv()*v
z=z0
sums={k:S.Integer(0) for k in ('incident','reflected','terminal','ohmic','relaxation','storage','net')}
for pair,kick in zip(P,kicks):
 a=amp*S.Matrix(pair);z1=T*z+kick;mid=(z+z1)/2;e=mid[:2,:];vel=mid[6:8,:];b=e-a
 d={'incident':D*a.dot(a)/Z,'reflected':D*b.dot(b)/Z,'terminal':D*G*e[1]**2,
  'ohmic':D*q(1,5)*e.dot(e),'relaxation':D*q(4,9)*vel.dot(vel), 'storage':S.factor(energy(z1,M)-energy(z,M))}
 d['net']=d['incident']-d['reflected']
 assert S.factor(d['net']-sum(d[k] for k in ('terminal','ohmic','relaxation','storage')))==0
 for k in sums:sums[k]+=d[k]
 z=z1
assert z==z0 and sums['storage']==0
assert S.factor(sums['net']-sums['terminal']-sums['ohmic']-sums['relaxation'])==0
print('exact pass',flush=True)
eta=sums['terminal']/sums['incident']
print('ETA',float(eta),'capture',float(sums['net']/sums['incident']),'ratio',float(sums['terminal']/sums['net']),flush=True)
res={'status':'PASS','Z':str(Z),'G':str(G),'amplitude':str(amp),'incident':float(sums['incident']), 'reflected':float(sums['reflected']), 'terminal':float(sums['terminal']), 'ohmic':float(sums['ohmic']),'relaxation':float(sums['relaxation']),'net':float(sums['net']), 'eta':float(eta),'capture':float(sums['net']/sums['incident']), 'terminal_per_net':float(sums['terminal']/sums['net']),'observability_two_step_rank':rank,'storage_exact_zero':True,'energy_residual_exact_zero':True,'restored_exact':True}
print(json.dumps(res,indent=2),flush=True)
