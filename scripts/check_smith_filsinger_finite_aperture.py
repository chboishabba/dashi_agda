"""Finite geodesic aperture of the original l=1 shell and XCIII-XCV receiver.
Normalized port scale fixture, not actual plate/electrode or calibrated source.
Argument: pinned metric-charge checker (original native matrices).
"""
import hashlib,sys,json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
raw=Path(sys.argv[1]).read_bytes();blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
assert blob=='1f3ee2625ede999147386b8f94e9078d29c94e65'
env={};exec(compile(raw.decode().split('rows=[run')[0],sys.argv[1],'exec'),env)
Da,L,N0,Ac,Kc,W,loss,Dloss=[env[k] for k in ('Da','L','N0','Ac','K','W','loss','Dloss')]
# Original angular and radial equations transcribed from pinned layered shell.
I=np.eye(6);axis=np.ones(3)/np.sqrt(3);X=np.cross(axis,np.eye(3)).T
K=np.block([[np.zeros((3,3)),-X/2],[X/2,np.zeros((3,3))]])
J=np.block([[np.zeros((3,3)),np.eye(3)],[-np.eye(3),np.zeros((3,3))]]) # B=[n cross,P], n cross P=T; n cross T=-P
R=6371000.;height=110000.;mu=4*np.pi*1e-7;eps=8.8541878128e-12;ya=1/(mu*1e6);yg=.1
# Geodesic integral: for TE -theta axis, TM endpoint difference.
# Stable cross/norm and endpoint z difference for small apertures.
def overlap(area,aspect):
    target=area/R**2
    def solid(y):return 4*np.arctan(aspect*y*y/np.sqrt(1+(aspect*aspect+1)*y*y))
    y=brentq(lambda y:solid(y)-target,0,2*np.sqrt(target/aspect),xtol=1e-25);x=aspect*y
    v=np.array([[a,b,1.] for b in (-y,y) for a in (-x,0,x)]);v/=np.linalg.norm(v,axis=1)[:,None]
    rows=[]
    for a,b in env['edges']:
        u,t=v[a],v[b];cross=np.cross(u,t);length=np.linalg.norm(cross);theta=np.arctan2(length,u@t)
        delta=t-u;delta[2]=-(delta[:2]@(t[:2]+u[:2]))/(t[2]+u[2])
        rows.append(np.sqrt(1.5)*np.r_[-theta*cross/length,delta])
    return np.array(rows),solid(y)*R**2

def shell(f):
    w=2*np.pi*f
    def layer(r0,r1,sigma,typ):
        a0=sigma+1j*w*eps
        def mat(r):
            a,b=(1j*w*mu,a0+2/(1j*w*mu*r*r)) if typ=='TE' else (1j*w*mu+2/(a0*r*r),a0)
            return np.array([[0,-a*ya],[-b/ya,0]],complex)
        sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(r0,r1),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12)
        assert sol.success;return sol.y[:,-1].reshape(2,2)
    mats={t:layer(R+height/2,R+height,1e-9,t)@layer(R,R+height/2,0,t) for t in ('TE','TM')}
    A,B,C,D=[np.diag(np.repeat([mats[t][i,j] for t in ('TE','TM')],3)) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    z=f/7.83;S=2*(I+.5*K)+J+1j*z*1.5/(4-z*z+1j*2*z/3)*I;U=I+S
    M=U@(A-B*yg)-(C-D*yg);Z=np.linalg.solve(M,D-U@B);V=np.linalg.solve(M,2*I)
    return A,B,C,D,S,Z,V

# Four active-edge effort driven native system, retain b, P, V and circuit.
# Frequency clock assumed tau=2pi*7.83*t; circuit current units chosen to
# make e^H i normalized work (physical current conversion not measured).
def native(f,e):
    w=f/7.83;E=L.T@e;h=-Da@e/(1.5j*w);p=1.5*E/(4-w*w+2j*w/3);v=1j*w*p
    beta=10.;rad=np.sqrt(.03);c=np.linalg.solve(1j*w*np.eye(9)-Ac,beta*rad*Kc.T@E/2);jc=beta*rad*Kc@c
    i=Dloss@e+L@(v+jc)+1j*w*(np.linalg.solve(N0,e)+L@p)-L@v-Da.T@h
    # displacement derivative contains Pdot once; displayed cancellation only.
    useful=.52*abs(c[-1])**2;heat=np.vdot(e,Dloss@e).real+4/9*np.vdot(v,v).real+np.vdot(c,loss@c).real-useful
    assert abs(np.vdot(e,i).real-useful-heat)<1e-8*max(1,abs(np.vdot(e,i)))
    return i,useful,heat
# Exact work adjoint and angular curl identities. No silent clamp of external traces.
T=s.Matrix(4,6,s.symbols('t:24',real=True));a=s.Matrix(s.symbols('a:6',real=True));j=s.Matrix(s.symbols('j:4',real=True))
assert (T*a).dot(j)==s.expand(a.dot(T.T*j)) or s.expand((T*a).dot(j)-a.dot(T.T*j))==0
rows=[]
for f in (.005,.05,3.915,7.83):
    A,B,C,D,S,Z,V=shell(f);Hr=(Z+Z.conj().T)/2;ev,U=np.linalg.eigh(Hr);assert min(ev)>0
    Hroot=(U*np.sqrt(ev))@U.conj().T;Hinv=(U/np.sqrt(ev))@U.conj().T
    Y=np.column_stack([native(f,e)[0] for e in np.eye(4)]);assert np.linalg.eigvalsh((Y+Y.conj().T)/2).min()>-1e-9
    for area in (1.,1e6,1e10):
     for aspect in (1.,1.5,(1+np.sqrt(5))/2):
        Tall,actual=overlap(area,aspect);T=Tall[:4];assert abs(actual/area-1)<1e-10
        # TM part integrates an exact gradient around both original faces.
        assert np.max(abs(env['D']@Tall[:,3:]))<1e-14
        # Reverse solve in power-whitened attainable current subspace; explicit SVD rank tolerance.
        Q,sv,_=np.linalg.svd(Hroot@T.T,full_matrices=False);rank=int(sum(sv>sv[0]*1e-12));Q=Q[:,:rank]
        Jload=T.T@Y@T
        for label,ei in [('TE_x',I[:,0]),('TM_y',I[:,4])]:
            voc=V@ei;field=np.linalg.solve(I+Z@Jload,voc);edge=T@field;i,useful,heat=native(f,edge);j=T.T@i
            full=np.vdot(voc,np.linalg.solve(Hr,voc)).real/4
            cap=np.linalg.norm(Q.conj().T@Hinv@voc)**2/4
            jopt=Hinv@Q@(Q.conj().T@Hinv@voc)/2
            residual=Hinv@voc-Q@(Q.conj().T@Hinv@voc)
            assert abs(full-cap-np.vdot(residual,residual).real/4)<1e-12
            assert abs(np.vdot(jopt,voc-Z@jopt).real-cap)<1e-10
            load=np.vdot(edge,i).real;assert abs(load-np.vdot(field,j).real)<1e-9
            h0=-yg*field-j;e1=A@field+B@h0;h1=C@field+D@h0
            ref=np.linalg.norm(e1-ei)**2;sheet=np.vdot(e1,S@e1).real;ground=yg*np.vdot(field,field).real;radial=np.vdot(field,h0).real-np.vdot(e1,h1).real
            err=1-ref-sheet-ground-radial-load
            assert abs(err)<1e-9 and abs(load-useful-heat)<1e-9 and load<=cap+1e-9
            # Retain external clamped-edge voltage mismatch; not same physical boundary.
            rows.append(dict(f=f,area=area,aspect=aspect,source=label,rank=rank,singular=sv.tolist(),full=full,restricted_ideal=cap,load=load,useful=useful,receiver_heat=heat,reflected=ref,sheet=sheet,ground=ground,radial=radial,ledger_error=err,unused_edge_norm=np.linalg.norm(Tall[4:]@field),backreaction_norm=np.linalg.norm(Z@j)))
print(json.dumps(dict(status='CONDITIONAL_FINITE_GEODESIC_APERTURE',donor_blob=blob,rows=rows,scope='Only l=1 exterior, assumed scalar clock/port scale, four-edge voltage driven off-guard native linear circuit; passive nonlocal Galerkin feedback. Clamped external trace not welded; no conductor boundary solve, real source or physical output. Ideal rank subspace comparator does not constrain current norm.'),indent=2))
