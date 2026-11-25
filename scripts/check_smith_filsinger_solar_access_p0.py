"""Solar-access P0: source-loaded resonant-mode comparison, not a calibrated Maxwell solver.
Classical coupled-mode/action balance, equal-area loop aperture and Hopf DC null.
All adjustable coupling and loss values are declared dimensionless test fixtures.
"""
import json, math
import sympy as S
import numpy as np
from numpy.polynomial.legendre import leggauss
Q=S.Rational
# a = source mode; b = same-frequency receiver; c = upconverted receiver.
# Energy per action is omega_s or omega_r. The source wave has unit action flux.
e,i,gd,gu,d,u,eta,ws,wr,a,b,c,src=S.symbols('e i gd gu d u eta ws wr a b c src', real=True)
# real rotating-frame signed quadratures: source equation e+i damping,
# reciprocal couplings gd,gu; receiver equations b'=gd*a-d*b, c'=gu*a-u*c.
fa=src-(e+i)*a-gd*b-gu*c; fb=gd*a-d*b; fc=gu*a-u*c
pump=2*(wr-ws)*gu*a*c
assert S.expand(2*ws*a*fa+2*ws*b*fb+2*wr*c*fc-(2*ws*src*a-2*ws*(e+i)*a*a-2*ws*d*b*b-2*wr*u*c*c+pump))==0
# Use gamma_ext=1, gamma_internal=1/4, sqrt(2)*s=1 with incident action=1/2.
# Normalize useful results by incident energy, not by arbitrary source voltage.
E=Q(1);I=Q(1,4);D=U=Q(1);eff=Q(9,10)
def exact(gd,gu,r,on):
    a=Q(on)/(E+I+gd*gd/D+gu*gu/U);b=gd*a/D;c=gu*a/U
    inc=Q(on,2);refl=(Q(on)-2*a)**2/2
    direct=2*D*b*b;converted=2*U*c*c*r;pc=2*(r-1)*gu*a*c
    internal=2*I*a*a;load=eff*(direct+converted);loss=(1-eff)*(direct+converted)+internal
    assert S.cancel(inc-refl+pc-load-loss)==0
    return {'incident':inc,'reflection':refl,'natural_net':inc-refl,'pump_conversion':pc,'useful':load,'heat':loss,'net_useful':load-pc,'direct_action':direct,'converted_action':2*U*c*c}
# Exact optimum for source-net absorption, gd^2+gu^2=e-i, if nonnegative.
q=S.symbols('q',nonnegative=True);reflect=(1-2/(E+I+q))**2/2
assert S.diff(reflect,q).subs(q,E-I)==0 and reflect.subs(q,E-I)==0
# Upconversion path alone: useful minus conversion power, per received action.
r=S.symbols('r',positive=True);assert S.expand(eff*r-(r-1)-(1-r/10))==0
assert (1-Q(1,1000))==Q(999,1000)
# Equal physical area planar loops, incident B normal; k dimensionless per sqrt(area).
# Flux form factor from integrating plane wave over rectangular aperture.
def aperture(aspect,k,theta):
    lx=math.sqrt(aspect);ly=1/lx
    return float(np.sinc(k*lx*math.cos(theta)/(2*math.pi))*np.sinc(k*ly*math.sin(theta)/(2*math.pi)))
# Two upstream pathways kept separate; 1 Hz is illustrative ULF, not a site measurement.
# Include half-Schumann diagnostic rather than claim a real mode exists there.
freqs={'solar_ULF_fixture':Q(1),'lightning_Schumann_fixture':Q(39,5),'half_Schumann_hypothesis':Q(39,10)}
rows=[]
for name,f in freqs.items():
    ratio=Q(7800)/f
    for aspect in (1,1.5,(1+math.sqrt(5))/2):
        # k=0 physical long-wave limit; k=1 diagnostic finite phase-gradient case.
        for k in (0.,1.):
            ap=aperture(aspect,k,0.); g=Q(str(round(ap,8)))
            for route in ('controlled_direct','upconversion'):
                worlds={}
                for label,p,n in [('A',0,0),('B',1,0),('C',0,1),('D',1,1)]:
                    # Direct route: same-frequency admittance control; its actuation cost is unknown.
                    # Upconversion route: retain the direct background, open a distinct converted path.
                    gd=g*(Q(1) if p and route=='controlled_direct' else Q(1,10));gu=g if p and route=='upconversion' else Q(0)
                    worlds[label]=exact(gd,gu,ratio,n)
                C=worlds['C'];W=worlds['D'];assert worlds['A']['useful']==worlds['B']['useful']==0
                rows.append(dict(source=name,frequency=float(f),ratio=float(ratio),aspect=aspect,k=k,aperture=ap,route=route,worlds={k:{a:float(b) for a,b in v.items()} for k,v in worlds.items()},delta_natural=float(W['natural_net']-C['natural_net']),incremental_net_budget=float(W['net_useful']-C['net_useful']),absolute_net_budget=float(W['net_useful'])))
# Geometry negative control: actual donor field h(tau)B from Hopf369 P0E/F.
# Compact support tau>=1/2 lies inside radius sqrt(3+2sqrt(2))=1+sqrt(2).
# div(hB)=0 by B.grad(tau)=0; integral B_h=0 for compact solenoidal B_h.
# Numerically integrate signed B_h Fourier overlap in a common cube, separately
# from planar loops (different resources; no cross-family ranking claimed).
def hopf(n):
    x,w=leggauss(n);R=1+math.sqrt(2);x=x*R;w=w*R
    X,Y,Z=np.meshgrid(x,x,x,indexing='ij');W=w[:,None,None]*w[None,:,None]*w[None,None,:]
    den=1+X*X+Y*Y+Z*Z;tau=4*(X*X+Y*Y)/den**2
    h=np.zeros_like(tau);mask=tau>.5;h[mask]=np.exp(-1/(tau[mask]-.5));h*=1/math.sqrt(float(np.sum(W*h*h*(64/den**4))))
    B=np.array([2*X*Z-2*Y,2*X+2*Y*Z,1-X*X-Y*Y+Z*Z])*8*h/den**3
    integ=[float(np.sum(W*b)) for b in B]; norm=math.sqrt(float(np.sum(W*np.sum(B*B,axis=0))))
    out=[]
    for k in (0,.01,.1,1,2):
        z=np.sum(W*B[1]*np.exp(1j*k*X))/math.sqrt((2*R)**3)
        out.append({'k':k,'signed_overlap':[float(z.real),float(z.imag)],'magnitude':float(abs(z))})
    return {'quadrature_order':n,'volume_L2_norm':norm,'mean_integral':integ,'overlaps':out}
hopf_rows=[hopf(n) for n in (32,48,64)]
# SI source-side scale checks: NOAA typical n=5/cm^3, v=375 km/s;
# Portishead typical horizontal magnetic ASD ~0.5--1 pT/sqrt(Hz).
# Loop emf from a deliberately assumed 1 pT RMS in selected band, 1 m^2-turn,
# aligned uniform flux, series resistance 1 ohm, ideal reactance compensation.
mp=1.67262192369e-27;n=5e6;v=375e3;flux=.5*mp*n*v**3
emf=2*math.pi*7.8*1e-12;cap=emf**2/4
result={'status':'SOURCE_LOADED_NORMALIZED_MODEL_AND_SI_SCALE_DIAGNOSTIC','world_rows':rows,'hopf_overlap':hopf_rows,'si':{'upstream_proton_kinetic_flux_W_m2':flux,'illustrative_loop_open_emf_rms_V':emf,'illustrative_loop_available_W':cap},'scope':{'source_to_ground_transfer_calibrated':False,'actual_HF_actuator_cost_known':False,'direct_control_is_ideal_admittance_change_not_demonstrated_HF':True,'upconversion_model':'action-conserving resonant frequency conversion, pump work exactly paid; additional pump overhead omitted','same_source_receiver_weld':False,'hopf_loop_comparable_resources':False,'no_measured_extraction':True},'sources':['https://www.spaceweather.gov/content/space-weather-glossary','https://doi.org/10.3390/atmos13010038','https://doi.org/10.1029/2025GL118532']}
print(json.dumps(result,indent=2))
