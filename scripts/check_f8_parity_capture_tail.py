"""F8 original mode3: signed parity/characteristic receiver and radial tail algebra.
Run with --checkpoint/--sidecar/--production-json on original capture files.
Default exact algebra + manufactured packet only; no original production claim.
"""
import argparse,hashlib,json,math
from pathlib import Path
import numpy as np
import sympy as S


def geometry_rows(t):
    # Literal existing warp_native_geometric_receiver.rows, independent check
    # against that source is made in capture mode.
    b=1/t;v=-1/math.sqrt(1+t*t);acc=t**3/(1+t*t)**2;s=1-v*v
    beta=math.sqrt(1+t*t)/t;J=-1/(t*math.sqrt(1+t*t))
    A,B,D,E,Y,L,X=np.eye(7)
    F=v*A+s*D;R=-B+2*v*E+s*Y+(acc-3/b)*D+L
    box=-B+2*v*E+s*Y+acc*D+L
    N=v*v*B+2*v*s*E+s*s*Y-v*v*acc*D
    return np.array([-b*b*(beta*beta*B+J*A+L)/4,-b*b*(beta*beta*B+J*A+X)/4,b*b*(-N/(2*s)+box/6),-b*b*(beta*beta*B+(J+2*beta)*A-L)/2,F,R])


def radial_rows(r,dr,eps,nr):
    j=math.floor(r/dr);q=r/dr-j;ids=np.arange(j-1,j+3)
    if ids[0]<0 or ids[-1]>=nr-1:raise ValueError('receiver outside active cubic stencil')
    w=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,-(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
    dw=np.array([-(3*q*q-6*q+2)/6,(3*q*q-4*q-1)/2,(-3*q*q+2*q+2)/2,(3*q*q-1)/6])/dr
    dd=np.array([1-q,3*q-2,1-3*q,q])/dr**2
    fac=(r/eps)**np.arange(0,6,2)
    L=np.stack([dd+(2*l+2)*dw/r for l in (0,2,4)])
    X=np.stack([dd+2*l*dw/r+l*(l-1)*w/r**2 for l in (0,2,4)])
    return ids,fac[:,None]*w,fac[:,None]*L,fac[:,None]*X


def packets(U,P,M,W,Pt,Mt,Wcentral_dot,force,dr,dy,t,r,eps):
    """Same central temporal derivative for all 3 packets; rate alternative separate.
    Inputs mode,normal,radial. Force is original common bulk stage force.
    No claim exact stencil equality in float; signed discrepancy is retained.
    """
    if U.ndim!=3 or U.shape[0]!=3 or U.shape[1]<5 or any(x.shape!=U.shape for x in (P,M,W,Pt,Mt,force)) or Wcentral_dot.shape!=U[:,0,:].shape:raise ValueError('state shape')
    if not all(np.isfinite(x).all() for x in (U,P,M,W,Pt,Mt,force,Wcentral_dot)):raise ValueError('nonfinite packet')
    v=-1/math.sqrt(1+t*t);a,c=1+v,1-v;acc=t**3/(1+t*t)**2
    N=(P-M)/2;Nt=(Pt-Mt)/2
    q1=N[:,1,:]-(U[:,2,:]-U[:,0,:])/(2*dy)
    q3=N[:,3,:]-(U[:,4,:]-U[:,2,:])/(2*dy)
    qt1=Nt[:,1,:]-(W[:,2,:]-W[:,0,:])/(2*dy)
    raw=[(-3*U[:,0,:]+4*U[:,1,:]-U[:,2,:])/(2*dy),(-3*W[:,0,:]+4*W[:,1,:]-W[:,2,:])/(2*dy),(U[:,2,:]-2*U[:,1,:]+U[:,0,:])/dy**2]
    even=[(U[:,2,:]-U[:,0,:])/(2*dy),(W[:,2,:]-W[:,0,:])/(2*dy),(U[:,4,:]-2*U[:,2,:]+U[:,0,:])/(4*dy**2)]
    char=[N[:,0,:],Nt[:,0,:],(Pt[:,0,:]-force[:,0,:])/(2*a)+(Mt[:,0,:]-force[:,0,:])/(2*c)]
    # Exact even identities with actual interior signed Q retained (not silently zero).
    e2=(Pt[:,2,:]-force[:,2,:])/(2*a)+(Mt[:,2,:]-force[:,2,:])/(2*c)
    parity_defects=[even[0]-N[:,1,:]+q1,even[1]-Nt[:,1,:]+qt1,even[2]-e2+(q3-q1)/(2*dy)]
    ids,w,L,X=radial_rows(r,dr,eps,U.shape[2])
    obs=lambda x,weights=w:np.sum(x[:,ids]*weights,axis=1)
    A=obs(W[:,0,:]);B=obs(Wcentral_dot);Bstage=obs((a*Pt[:,0,:]+c*Mt[:,0,:])/2+acc*N[:,0,:]);lap=obs(U[:,0,:],L);ax=obs(U[:,0,:],X)
    rows=geometry_rows(t);jets={name:np.stack([A,B,*[obs(x) for x in seq],lap,ax]) for name,seq in [('raw',raw),('even',even),('characteristic',char)]}
    out={k:rows@j for k,j in jets.items()};stage=jets['even'].copy();stage[1]=Bstage;out['even_stage_time']=rows@stage
    diff=jets['raw']-jets['even'];delta=rows@diff
    for k,o in out.items():
        res=o[2]-o[3]+(1/t+1/(2*t**3))*o[4]+o[5]/(3*t*t)
        scale=np.sum(abs(o),axis=0)+1e-300
        if np.any(abs(res)>2e-12*scale):raise ValueError('off-shell Weyl contraction '+k)
    if not np.allclose(out['raw']-out['even'],delta,rtol=2e-10,atol=2e-10*np.max(abs(out['raw'])+abs(out['even']))):raise ValueError('signed readout discrepancy')
    return dict(rows=['E4','legacy4','direct','SMS','F','R'],jets={k:x.tolist() for k,x in jets.items()},observations={k:x.tolist() for k,x in out.items()},raw_minus_even=delta.tolist(),raw_minus_even_normal_jets=diff[2:5].tolist(),stage_minus_central_Wt=(Bstage-B).tolist(),parity_identity_remainders=[float(np.max(abs(x[:,ids]))) for x in parity_defects],interior_Q_receiver=[obs(q1).tolist(),obs(q3).tolist()],interior_Qdot_receiver=obs(qt1).tolist(),radial_ids=ids.tolist())


def exact():
    n=0
    def eq(a,b=0):
        nonlocal n
        assert S.simplify(a-b)==0,(a,b);n+=1
    # P_yy expressed through time derivatives and K N, no K^2 source.
    a,c,ad,z,K,U,N,Pt,Ptt,Nt,Ny,Py,Ut=S.symbols('a c ad z K U N Pt Ptt Nt Ny Py Ut',nonzero=True)
    py=(Pt+K*U+3*N/z)/a
    pty=(Ptt+K*Ut+3*Nt/z-3*N*(a-1)/z**2-ad*py)/a
    pyy=(pty+K*N+3*Ny/z-3*N/z**2)/a
    eq(a*py-Pt-K*U-3*N/z)
    eq(a*pty+ad*py-Ptt-K*Ut-3*Nt/z+3*N*(a-1)/z**2)
    eq(a*pyy-pty-K*N-3*Ny/z+3*N/z**2)
    # Reversed energy boundary flux, outgoing opposite to physical branch.
    p,m,g=S.symbols('p m g');flux=(a*a*p*p-c*c*m*m)/2
    eq(flux.subs(p,g)-a*a*g*g/2,-c*c*m*m/2)
    eq((-flux).subs(m,g)-c*c*g*g/2,-a*a*p*p/2)
    # Dyadic radial frequency R, source tail R^-1/2; wall trace R^-1/2
    # and annulus point evaluation R^1/2 cancel, leaving source tail.
    R=S.symbols('R',positive=True)
    eq(R**S.Rational(1,2)*R**S.Rational(-1,2)*R**S.Rational(-1,2),1/S.sqrt(R))
    eq(S.simplify(1/(1-1/S.sqrt(2))),2+S.sqrt(2))
    # Trace optimization: ||f(0)||² <= Y^-1||f||²+2||f||||f_y||.
    x,y,z0=S.symbols('x y z0',real=True);eq((x-y)**2+2*x*y,x*x+y*y)
    # Exact interior parity residual for arbitrary nodes including nonzero Q.
    h,u0,u1,u2,u3,u4,n1,n3=S.symbols('h u0 u1 u2 u3 u4 n1 n3',nonzero=True)
    q1=n1-(u2-u0)/(2*h);q3=n3-(u4-u2)/(2*h)
    eq((u4-2*u2+u0)/(4*h*h)-(n3-n1)/(2*h)+(q3-q1)/(2*h))
    return n


def manufactured():
    # Deliberately nonzero parity and wall residual, no physics inference.
    rng=np.random.default_rng(369);shape=(3,7,18);U,P,M,Pt,Mt,force=[rng.normal(size=shape) for _ in range(6)]
    v=-1/math.sqrt(145);a,c=1+v,1-v;W=(a*P+c*M)/2;h=.02
    # Make interior stage rows exactly source-form; arbitrary boundary rates.
    Pt[:,1:-1,:]=a*(P[:,2:,:]-P[:,:-2,:])/(2*h)+force[:,1:-1,:]
    Mt[:,1:-1,:]=-c*(M[:,2:,:]-M[:,:-2,:])/(2*h)+force[:,1:-1,:]
    out=packets(U,P,M,W,Pt,Mt,rng.normal(size=(3,18)),force,.01,h,12.,.083,.04)
    assert max(out['parity_identity_remainders'])<1e-9
    assert np.max(abs(np.array(out['raw_minus_even'])))>1
    assert np.max(abs(np.array(out['interior_Q_receiver'])))>1
    return dict(parity_remainders=out['parity_identity_remainders'],raw_direct_gap=out['raw_minus_even'][2])


def capture(checkpoint,sidecar,production):
    from check_f8_p0_original_same_clock_state import read
    import ksw668_f8_tt_multipole as original
    stage,F=original.stage,original.F
    from warp_native_geometric_receiver import rows
    verified=read(checkpoint,sidecar,production)
    if hashlib.sha256(Path(original.__file__).read_bytes()).hexdigest()!=verified['source_sha256']['ksw668_f8_tt_multipole.py']:
        raise ValueError('local stage differs from captured original source')
    prod=json.loads(Path(production).read_text());t=prod['receiver_t'];dt=prod['step_time'];eps=prod['eps']
    np.testing.assert_allclose(geometry_rows(t),rows(t),rtol=2e-14,atol=1e-15)
    with np.load(sidecar,allow_pickle=False) as z:
        U,P,M,W,source=[z[k].copy() for k in ('U','P','M','Ut','source')];dr,dy,b,v,amp=[float(z[k].item()) for k in ('dr','dy','b','v','amp')]
    with np.load(checkpoint,allow_pickle=False) as z:
        nextP=z['P'][:,0,:].copy();nextM=z['M'][:,0,:].copy();prevW=z['w2'].copy()
    tn=t
    for _ in range(7):tn-=(F(tn)-F(t)-dt)/(math.sqrt(1+tn*tn)/tn**2)
    vn=-1/math.sqrt(1+tn*tn);nextW=((1+vn)*nextP+(1-vn)*nextM)/2
    nextW[:,-1]=0;central=(nextW-prevW)/(2*dt)
    nr=U.shape[-1];cp=np.zeros((3,nr));cm=cp.copy();j=np.arange(1,nr)
    for i,d in enumerate((3,7,11)):
        den=(j+.5)**d-(j-.5)**d;cp[i,1:]=d*(j+.5)**(d-1)/den;cm[i,1:]=d*(j-.5)**(d-1)/den
    Wu,Pt,Mt=[np.zeros_like(U) for _ in range(3)];stage(U,P,M,Wu,Pt,Mt,dr,dy,b,v,amp,source,cp,cm,3)
    np.testing.assert_allclose(Wu,W,rtol=1e-12,atol=1e-13)
    force=np.zeros_like(U);N=(P-M)/2
    for i,d in enumerate((3,7,11)):
        force[i,:,0]=2*d*(U[i,:,1]-U[i,:,0])/dr**2
        force[i,:,1:-1]=(cp[i,1:-1]*(U[i,:,2:]-U[i,:,1:-1])-cm[i,1:-1]*(U[i,:,1:-1]-U[i,:,:-2]))/dr**2
    force-=3*N/(b+dy*np.arange(U.shape[1]))[None,:,None];force[:,:,-1]=0
    outputs={}
    for label,r,prefix in [('near',prod['nominal_receiver_r'],'receiver'),('far',prod['far_receiver_grid_r'],'far')]:
        out=packets(U,P,M,W,Pt,Mt,central,force,dr,dy,t,r,eps);o=out['observations']['raw']
        for row,key in [(0,'intrinsic_4D'),(3,'projected_5D')]:
            want=np.asarray(prod[prefix+'_mode_'+key+'_electric_Weyl_tangent']);got=np.asarray(o[row]);np.testing.assert_allclose(got,want,rtol=1e-9,atol=1e-12)
        outputs[label]=out
    return dict(source_identity=verified['source_sha256'],label=verified['source_label'],receivers=outputs,scope='original same-clock captured receiver only; no numerical continuum acceptance')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--checkpoint');p.add_argument('--sidecar');p.add_argument('--production-json');a=p.parse_args()
    if any((a.checkpoint,a.sidecar,a.production_json)):
        if not all((a.checkpoint,a.sidecar,a.production_json)):p.error('all three source-pinned inputs required')
        result=capture(a.checkpoint,a.sidecar,a.production_json)
    else:result=dict(exact_checks=exact(),manufactured=manufactured(),scope='exact algebra plus synthetic finite receiver packet; original capture not run')
    print(json.dumps(result,indent=2))
