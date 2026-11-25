"""Finite passive return and same-background angular refinement of pinned shell.
Arguments: current-budget, finite-aperture, metric-charge checkers.
Normalized Galerkin fixture, not an actual conductor or calibrated source.
"""
import sys, hashlib, json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss
p,a,m=sys.argv[1:4]
raw=Path(p).read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='97d67fa9e4af6f61835f766fbe89994a922c48cc'
old=sys.argv;sys.argv=[p,a,m];d={};exec(compile(raw.decode().split('\nrows=[];checks=[]')[0],p,'exec'),d);sys.argv=old
orig=d['d'];R,ht,mu,eps,ya,yg=[d[k] for k in ('R','ht','mu','eps','ya','yg')]
# Real harmonic homogeneous polynomials, orthonormal tangent gradients.
x=s.Matrix(s.symbols('x:3',real=True));ax=np.ones(3)/np.sqrt(3)
zz,ww=leggauss(12);nodes=[];weights=[]
for z,w in zip(zz,ww):
 for phi in 2*np.pi*np.arange(24)/24:
    nodes.append([np.sqrt(1-z*z)*np.cos(phi),np.sqrt(1-z*z)*np.sin(phi),z]);weights.append(w/48)
nodes=np.array(nodes);weights=np.array(weights)
funcs={}
for ell in (3,4):
    mons=[x[0]**i*x[1]**j*x[2]**(ell-i-j) for i in range(ell+1) for j in range(ell-i+1)]
    low=[(i,j,ell-2-i-j) for i in range(ell-1) for j in range(ell-1-i)]
    A=s.Matrix([[s.Poly(sum(s.diff(t,v,2) for v in x),*x).coeff_monomial(k) for t in mons] for k in low]);basis=A.nullspace();assert len(basis)==2*ell+1
    polys=[sum(c*t for c,t in zip(b,mons)) for b in basis]
    grad=s.Matrix([[s.diff(t,v) for t in polys] for v in x]);fun=s.lambdify(tuple(x),grad,'numpy')
    def rawgrad(n,fun=fun):return (np.eye(3)-np.outer(n,n))@np.array(fun(*n),float)
    gr=sum(w*(rawgrad(n).T@rawgrad(n)) for n,w in zip(nodes,weights));ev,U=np.linalg.eigh(gr);assert min(ev)>0
    transform=(U/np.sqrt(ev))@U.T
    funcs[ell]=lambda n,rawgrad=rawgrad,transform=transform:rawgrad(n)@transform

def angular(n,N):
    B=d['angular'](n)[:,:min(16,N)];cross=np.cross(n,np.eye(3)).T
    for ell in (3,4):
        if N>=2*ell*(ell+2):
            P=funcs[ell](n);B=np.column_stack((B,cross@P,P))
    return B
G=np.zeros((48,48));K=G.copy();J=G.copy()
for n,w in zip(nodes,weights):
    B=angular(n,48);X=np.cross(n,np.eye(3)).T;G+=w*B.T@B;K+=w*(ax@n)*B.T@B;J+=w*B.T@X@B
assert np.max(abs(G-np.eye(48)))<1e-13
assert np.max(abs(K[:16,:16]-d['K']))<1e-13 and np.max(abs(J[:16,:16]-d['J']))<1e-13

def shell(f,N):
    w=2*np.pi*f;mats=[]
    for ell in range(1,5):
     if 2*ell*(ell+2)>N:break
     for typ in ('TE','TM'):
        L=ell*(ell+1);M=np.eye(2,dtype=complex)
        for r0,r1,sg in ((R,R+ht/2,0),(R+ht/2,R+ht,1e-9)):
            aa=sg+1j*w*eps
            def mat(r):
                a,b=(1j*w*mu,aa+L/(1j*w*mu*r*r)) if typ=='TE' else (1j*w*mu+L/(aa*r*r),aa)
                return np.array([[0,-a*ya],[-b/ya,0]],complex)
            sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(r0,r1),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12)
            assert sol.success;M=sol.y[:,-1].reshape(2,2)@M
        mats += [M]*(2*ell+1)
    A,B,C,D=[np.diag([M[i,j] for M in mats]) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    z=f/7.83;I=np.eye(N);S=2*(I+.5*K[:N,:N])+J[:N,:N]+1j*z*1.5/(4-z*z+1j*2*z/3)*I;U=I+S
    M=U@(A-B*yg)-(C-D*yg);Z=np.linalg.solve(M,D-U@B);V=np.linalg.solve(M,2*I)
    assert min(np.linalg.eigvalsh((Z+Z.conj().T)/2))>0
    return A,B,C,D,S,Z,V

def overlap(area,aspect,N,order=8):
    T=d['overlap'](area,aspect,min(N,16))
    if N<=16:return T
    target=area/R**2
    def solid(y):return 4*np.arctan(aspect*y*y/np.sqrt(1+(aspect*aspect+1)*y*y))
    y=brentq(lambda y:solid(y)-target,0,2*np.sqrt(target/aspect),xtol=1e-25);xx=aspect*y
    v=np.array([[a,b,1.] for b in (-y,y) for a in (-xx,0,xx)]);v/=np.linalg.norm(v,axis=1)[:,None]
    zz,ww=leggauss(order);rows=[]
    for aa,bb in orig['env']['edges']:
        n,t=v[aa],v[bb];cross=np.cross(n,t);u=cross/np.linalg.norm(cross);theta=np.arctan2(np.linalg.norm(cross),n@t);tangent=np.cross(u,n)
        out=np.zeros(N-16)
        for z,w in zip(zz,ww):
            arg=theta*(z+1)/2;nn=n*np.cos(arg)+tangent*np.sin(arg);dn=np.cross(u,nn)
            out+=w*theta/2*(dn@angular(nn,N)[:,16:])
        rows.append(out)
    return np.column_stack((T,rows))

# Full seven-edge receiver with finite passive return Hodge and conductance.
env=orig['env'];D0=env['D'];G0=env['G'];L=np.eye(7)[:,:2];Ac=env['Ac'];Kc=env['K'];loss=env['loss'];beta=10.;rad=np.sqrt(.03)
assert np.max(abs(D0@G0))==0

def native(f,e,g):
    w=f/7.83;E=L.T@e;h=-D0@e/(1.5j*w);p=1.5*E/(4-w*w+2j*w/3);v=1j*w*p
    c=np.linalg.solve(1j*w*np.eye(9)-Ac,beta*rad*Kc.T@E/2);jc=beta*rad*Kc@c
    mass=np.diag([2,2,.1,.1,1,1,1]);C=np.diag([.2,.2,20/9,20/9,g,g,g]);disp=mass@e+L@p
    conduction=C@e+L@jc;i=conduction+1j*w*disp-D0.T@h;rho=G0.T@disp
    useful=.52*abs(c[-1])**2;ret=g*np.linalg.norm(e[4:])**2
    heat=np.vdot(e,C@e).real+4/9*np.vdot(v,v).real+np.vdot(c,loss@c).real-useful
    charge=np.linalg.norm(1j*w*rho+G0.T@(conduction-i));assert abs(sum(rho))<1e-10
    assert abs(np.vdot(e,i).real-useful-heat)<1e-10 and charge<1e-10
    return i,useful,heat,ret,charge
# Exact charge continuity on arbitrary full cochains, no extra clamp current.
Gs=s.Matrix(G0.astype(int));Ds=s.Matrix(D0.astype(int));hs=s.Matrix(s.symbols('h:2'));assert Gs.T*Ds.T*hs==s.zeros(6,1)
rows=[];max_quad=0.
for f in (.005,.05,3.915,7.83):
 for N in (6,16,30,48):
    A,B,C,D,S,Z,V=shell(f,N)
    if N<=16:assert max(np.max(abs(x-y)) for x,y in zip((A,B,C,D,S,Z,V),d['shell'](f,N)))<1e-11
    for area in (1.,1e6,1e10):
     for aspect in (1.,1.5,(1+np.sqrt(5))/2):
        T=overlap(area,aspect,N);Tfine=overlap(area,aspect,N,16);max_quad=max(max_quad,np.max(abs(T-Tfine)));assert np.max(abs(T-Tfine))<1e-12
        for g in (.1,1.,10.):
            Y=np.column_stack([native(f,e,g)[0] for e in np.eye(7)]);assert min(np.linalg.eigvalsh((Y+Y.conj().T)/2))>0
            Zport=T@Z@T.T;M=np.eye(7)+Zport@Y
            for src in (-1,0,4):
                ei=np.eye(N)[:,src] if src>=0 else np.zeros(N);voc=V@ei;e=np.linalg.solve(M,T@voc);i,useful,heat,ret,charge=native(f,e,g);j=T.T@i;field=voc-Z@j
                assert np.linalg.norm(e-T@field)<1e-10
                h0=-yg*field-j;e1=A@field+B@h0;h1=C@field+D@h0;ref=np.linalg.norm(e1-ei)**2;sheet=np.vdot(e1,S@e1).real;ground=yg*np.vdot(field,field).real;radial=np.vdot(field,h0).real-np.vdot(e1,h1).real;load=np.vdot(e,i).real
                err=np.vdot(ei,ei).real-ref-sheet-ground-radial-load;assert abs(err)<1e-9 and abs(load-useful-heat)<1e-10
                if src<0:assert np.linalg.norm(i)==0 and useful==0
                # Compare outgoing field with no receiver, retain signed interference.
                hbare=-yg*voc;outbare=A@voc+B@hbare-ei;delta=e1-ei-outbare
                scatter=np.vdot(delta,delta).real;cross=2*np.vdot(outbare,delta).real
                assert abs(ref-np.vdot(outbare,outbare).real-scatter-cross)<1e-10
                rows.append(dict(f=f,N=N,area=area,aspect=aspect,g=g,src=src,useful=useful,load=load,return_heat=ret,current=float(np.linalg.norm(i)),return_current=float(np.linalg.norm(i[4:])),return_effort=float(np.linalg.norm(e[4:])),charge=charge,ledger=float(err),outgoing_higher=float(np.linalg.norm((e1-ei)[16:])**2),receiver_scattered=float(scatter),outgoing_cross=float(cross)))
print(json.dumps(dict(status='CONDITIONAL_FINITE_RETURN_ANGULAR_REFINEMENT',rows=rows,max_quadrature_difference=float(max_quad),max_charge=max(r['charge'] for r in rows),max_ledger=max(abs(r['ledger']) for r in rows)),indent=2))
