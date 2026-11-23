"""LXXX: local native mode-3, three-time, four-channel source VJP parity.

Reuses the original stage and #1530 warp_stage_adjoint.transpose. Observations
use the corrected spatial Delta3 (not the legacy Hxx), both E4/E5 Weyl
channels and stage-tangent variants. Five-step fixture, NOT full production
clock, certified floating adjoint, or continuum Weyl result. No CI.
"""
import math
import json
import numpy as np
from ksw668_f8_tt_multipole import stage
from warp_stage_adjoint import transpose


def geometry(nr,dr):
    cp=np.zeros((3,nr));cm=cp.copy()
    for q in range(3):
        d=3+4*q
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den
            cm[q,j]=d*(j-.5)**(d-1)/den
    return cp,cm


def clock():
    return [((.48,-.35,a),(.477,-.353,a*1.15),(.479,-.352,a*.92))
            for a in (-.08,-.15,-.2,-.12,-.04)]


def forward(src,cs,dt,dr,dy):
    cp,cm=geometry(src.shape[-1],dr)
    x=np.zeros((3,3,6,src.shape[-1]));hist=[x.copy()]
    def step(u,z):
        b,v,amp=z;du=np.empty_like(u)
        stage(*u,*du,dr,dy,b,v,amp,src,cp,cm,3)
        return u+dt*du
    for a0,a1,ah in cs:
        x1=step(x,a0)
        x2=.75*x+.25*step(x1,a1)
        x=x/3+2*step(x2,ah)/3
        hist.append(x.copy())
    return hist


def observer(r,dr,eps,dt,t,cs,nr):
    x=r/dr;ir=math.floor(x);q=x-ir
    assert 1<=ir and ir+2<nr
    w=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,
                -(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
    dw=np.array([-(3*q*q-6*q+2)/6,(3*q*q-4*q-1)/2,
                 (-3*q*q+2*q+2)/2,(3*q*q-1)/6])/dr
    dd=np.array([1-q,3*q-2,1-3*q,q])/dr**2
    S=math.sqrt(1+t*t)/t;Se=-1/(t*math.sqrt(1+t*t))
    vs=[cs[i][0][1] for i in (3,4)]+[cs[-1][1][1]]
    # Layout channel, ell, (prev,now,next), (U,P,M), mode, y, radial.
    out=np.zeros((4,3,3,3,3,6,nr))
    for iq in range(3):
        ell=2*iq;fac=(r/eps)**ell
        L=fac*(dd+(2*ell+2)*dw/r);U=fac*w
        for ch in range(4):
            is5=ch%2==1;tangent=ch>=2
            pref=-1/((2 if is5 else 4)*t*t)
            out[ch,iq,1,0,iq,0,ir-1:ir+3]+=pref*(-L if is5 else L)
            if not tangent:
                a=Se+2*S*is5
                weights=(S*S/dt**2-a/(2*dt),-2*S*S/dt**2,
                         S*S/dt**2+a/(2*dt))
                for n,b in enumerate(weights):
                    out[ch,iq,n,0,iq,0,ir-1:ir+3]+=pref*b*U
            else:
                weights=(-S*S/(2*dt),Se+2*S*is5,S*S/(2*dt))
                for n,b in enumerate(weights):
                    out[ch,iq,n,1,iq,0,ir-1:ir+3]+=pref*b*U*(1+vs[n])/2
                    out[ch,iq,n,2,iq,0,ir-1:ir+3]+=pref*b*U*(1-vs[n])/2
    return out,w,dw,dd,vs


def original_scalar(hist,r,dr,eps,dt,t,wd):
    """Independently evaluate original propagate.read_all scalar formulas."""
    w,dw,dd,vs=wd;x=r/dr;ir=math.floor(x)
    S=math.sqrt(1+t*t)/t;Se=-1/(t*math.sqrt(1+t*t))
    out=np.zeros((4,3))
    for q in range(3):
        ell=2*q;fac=(r/eps)**ell
        U=np.array([fac*np.dot(w,hist[n][0,q,0,ir-1:ir+3]) for n in (3,4,5)])
        L=fac*np.dot(dd+(2*ell+2)*dw/r,hist[4][0,q,0,ir-1:ir+3])
        dot=np.array([fac*np.dot(w,.5*((1+vs[k])*hist[n][1,q,0,ir-1:ir+3]+
                  (1-vs[k])*hist[n][2,q,0,ir-1:ir+3])) for k,n in enumerate((3,4,5))])
        HT=(U[2]-U[0])/(2*dt);HTT=(U[2]-2*U[1]+U[0])/dt**2
        A=S*S*HTT+Se*HT;AT=S*S*(dot[2]-dot[0])/(2*dt)+Se*dot[1]
        out[:,q]=[-(A+L)/(4*t*t),-(A+2*S*HT-L)/(2*t*t),
                  -(AT+L)/(4*t*t),-(AT+2*S*dot[1]-L)/(2*t*t)]
    return out


def source_vjp(obs,cs,dt,dr,dy):
    lam=obs[-1].copy();K=np.zeros((3,lam.shape[-1]))
    def adj(x,z):
        b,v,_=z
        return x+dt*transpose(x,dr,dy,b,v,3)
    for n in range(len(cs)-1,-1,-1):
        a0,a1,ah=cs[n]
        K+=(-4*ah[2]/dy)*(2*dt/3)*lam[2,:,0,:]
        l2=2*adj(lam,ah)/3
        K+=(-4*a1[2]/dy)*(dt/4)*l2[2,:,0,:]
        l1=adj(l2,a1)/4
        K+=(-4*a0[2]/dy)*dt*l1[2,:,0,:]
        lam=lam/3+.75*l2+adj(l1,a0)
        if n in (3,4):lam+=obs[n-3]
    K[:,-1]=0
    return K


def main():
    from warp_stage_adjoint import donor_parity
    donor_parity()
    rng=np.random.default_rng(20261123);cs=clock();dt=.00018;dy=.012
    report=[]
    for dr in (.008,.006):
        nr=9
        src=rng.normal(size=(3,nr));src[:,-1]=0
        src2=rng.normal(size=(3,nr));src2[:,-1]=0
        hist=forward(src,cs,dt,dr,dy);hist2=forward(src2,cs,dt,dr,dy)
        errors=[];interventions=[];scalar=[]
        for r in (4.35*dr,5.25*dr):
            O,w,dw,dd,vs=observer(r,dr,.04,dt,12.,cs,nr)
            oracle=original_scalar(hist,r,dr,.04,dt,12.,(w,dw,dd,vs))
            for ch in range(4):
                for q in range(3):
                    obs=O[ch,q]
                    direct=sum(float(np.vdot(obs[k],hist[k+3])) for k in range(3))
                    difference=sum(float(np.vdot(obs[k],hist2[k+3]-hist[k+3])) for k in range(3))
                    K=source_vjp(obs,cs,dt,dr,dy)
                    pred=float(np.vdot(K,src))
                    pred_difference=float(np.vdot(K,src2-src))
                    assert np.isclose(direct,oracle[ch,q],rtol=2e-7,atol=2e-8)
                    assert np.isclose(direct,pred,rtol=2e-7,atol=2e-8)
                    assert np.isclose(difference,pred_difference,rtol=2e-7,atol=2e-8)
                    scalar.append(abs(direct-oracle[ch,q]))
                    errors.append(abs(direct-pred))
                    interventions.append(abs(difference-pred_difference))
        assert len(errors)==24
        report.append(dict(dr=dr,observations=len(errors),
                           max_scalar_readback_error=max(scalar),
                           max_forward_vjp_error=max(errors),
                           max_intervention_vjp_error=max(interventions)))
    print(json.dumps(report,indent=2))
    print("PASS 48/48 source VJP & intervention comparisons; 48/48 scalar observers")
    return report


if __name__=="__main__":main()
