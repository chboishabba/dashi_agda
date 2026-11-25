"""Paid trajectory-controlled Lorentz actuator and reciprocal Hopf-loop comparator.
Dimensionless fixtures, not a calibrated material, GAMERA replay or full RMHD.
"""
import json
import numpy as np
import sympy as S
from scipy.integrate import solve_ivp
from scipy.linalg import solve_banded
q,v,y,w,rs,rl,k,m,om,Q,g,fs,fp=S.symbols('q v y w rs rl k m om Q g fs fp',real=True)
U=(v*v+k*q*q+m*(w*w+om*om*y*y)+g*q*q*y*y)/2
f=S.Matrix([v,fs-(rs+rl)*v-(k+g*y*y)*q,w,(fp-m*om*w/Q-m*om*om*y-g*q*q*y)/m])
assert S.simplify(S.Matrix([S.diff(U,x) for x in (q,v,y,w)]).dot(f)-fs*v-fp*w+(rs+rl)*v*v+m*om*w*w/Q)==0
# q is driven at normalized angular frequency 1; y=A cos(Omega t) is
# prescribed by an ideal force servo, not a free response to a pure HF tone.
# Signed Floquet sidebands 1+2nOmega, with real conjugate partners.
def response(O,N,on,source):
    A=np.sqrt(1.5)*on; shift=A*A/2; n=np.arange(-N,N+1); freq=1+2*n*O
    diag=.25+shift-freq*freq+2j*freq
    ab=np.zeros((3,2*N+1),complex);ab[1]=diag;ab[0,1:]=shift/2;ab[2,:-1]=shift/2
    b=np.zeros(2*N+1,complex);b[N]=source/np.sqrt(2)
    x=solve_banded((1,1),ab,b);vel=1j*freq*x
    src=2*np.real(np.conj(b[N])*vel[N]);load=2*np.vdot(vel,vel).real
    exchange=2*load-src # conservative actuator-to-slow work, signed
    # Independently compute -g<q*y^2*q'> = (g/2)<(y^2)'q^2>.
    # q^2 coefficient at +2Omega from positive and negative sideband families.
    c=2*np.sum(x[1:]*np.conj(x[:-1]));exchange_direct=shift*O*c.imag
    assert abs(exchange-exchange_direct)<2e-9,(O,exchange,exchange_direct)
    return dict(source=float(src),load=float(load),source_heat=float(load),exchange=float(exchange),edge_residual=float(abs(shift*x[0]/2)+abs(shift*x[-1]/2)),actuator_loss_numerator=float(O*shift))
rows=[]
for O in (20,1000,2000,1560000):
    C=response(O,8,0,1);D=response(O,8,1,1);fine=response(O,16,1,1)
    assert max(abs(D[k]-fine[k]) for k in ('load','source','exchange'))<1e-10
    budget=D['load']-C['load']-D['exchange'];assert budget>0
    threshold=D['actuator_loss_numerator']/budget
    for quality in (100,10000,1000000,100000000):
        worlds={}
        for label,on,source in [('A',0,0),('B',1,0),('C',0,1),('D',1,1)]:
            z=response(O,8,on,source);heat=z['actuator_loss_numerator']/quality;pump=z['exchange']+heat
            err=z['source']+pump-z['load']-z['source_heat']-heat
            assert abs(err)<1e-12
            worlds[label]=dict(**z,pump=float(pump),actuator_heat=float(heat),net=float(z['load']-pump),ledger_residual=float(err))
        rows.append(dict(Omega=O,Q=quality,Q_incremental_threshold=float(threshold),worlds=worlds,incremental_net=worlds['D']['net']-worlds['C']['net']))
# Actual original P0H uncut Hopf B_z on a transverse disk, rest coordinates.
r,z,R=S.symbols('r z R',positive=True);a=1+z*z
primitive=8*S.pi*r*r/(a+r*r)**2
assert S.simplify(S.diff(primitive,r)-2*S.pi*r*8*(a-r*r)/(a+r*r)**3)==0
phi=primitive.subs(r,R);assert S.simplify(S.diff(phi,z)+32*S.pi*R*R*z/(1+z*z+R*R)**3)==0
assert S.simplify(S.diff(phi,R).subs(R,S.sqrt(a)))==0
# A nonrelativistic generalized-coordinate model of a moving rigid donor.
# Reciprocity: emf=-Phi' zdot, mechanical force=i Phi'. Finite kinetic
# store pays work; resetting speed costs exactly the lost kinetic energy.
I,L,vel,M,dp,Rc,Rl=S.symbols('I L vel M dp Rc Rl',real=True)
assert S.expand(vel*I*dp+I*(-dp*vel-(Rc+Rl)*I)+(Rc+Rl)*I*I)==0
passes=[]
for radius in (.5,1,2,4):
 for load in (.1,1,10):
    mass=10.;L0=1.;Rc0=.1;scale=.1;initial=[-20.,.5,0.,0.,0.]
    def rhs(t,x):
        zz,vv,ii,_,_=x;dp=-scale*32*np.pi*radius**2*zz/(1+zz*zz+radius**2)**3
        return [vv,ii*dp/mass,(-dp*vv-(Rc0+load)*ii)/L0,load*ii*ii,Rc0*ii*ii]
    def end(t,x):return x[0]-20
    end.terminal=True;end.direction=1
    sol=solve_ivp(rhs,(0,200),initial,rtol=2e-10,atol=2e-12,events=end,max_step=.2)
    assert sol.success and len(sol.t_events[0])==1
    zz,vv,ii,useful,heat=sol.y[:,-1];kin0=mass*initial[1]**2/2;kin1=mass*vv*vv/2;store=L0*ii*ii/2
    residual=kin0-kin1-store-useful-heat;assert abs(residual)<1e-8
    passes.append(dict(radius=radius,load_R=load,kinetic_in=kin0,kinetic_out=float(kin1),useful=float(useful),copper=float(heat),coil_storage=float(store),residual=float(residual),minimum_velocity=float(min(sol.y[1])),reset_kinetic_cost=float(kin0-kin1)))
print(json.dumps(dict(status='CONDITIONAL_PAID_ACTUATOR_AND_RECIPROCAL_HOPF_PASS',actuator=rows,hopf=passes,scope='Servo prescribes y, force includes q^2 y backreaction; normalized m Omega^2=1, g=1; Fourier truncation numerical, not exact interval. No direct HF feedthrough to slow mode except parametric stiffness. Hopf comparator uses original uncut rest Bz, nonrelativistic rigid translation and generalized reciprocal force, not full loaded Maxwell/RMHD. No physical source calibration or net harvested solar work.'),indent=2))
