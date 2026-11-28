"""Octet constitutive chart and paid sideband replay of the pinned layered shell.
No physical HF-to-half-mode realization or calibrated source.
Arguments: layered checker path, OCT369 preflight path.
"""
import hashlib,sys,json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import solve

def blob(path):
    b=Path(path).read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
path,preflight=sys.argv[1:3]
assert blob(path)=='097cc72daff0ccb657972e9316a3f0244fb6591d'
assert blob(preflight)=='1f493bdedf3ca058470db4fe0154c13d4df905b4'
# Execute original angular and radial definitions, not its sweep.
old=sys.argv;sys.argv=[path,preflight];env={'__name__':'__donor__'}
exec(compile(Path(path).read_text().split('rows=[];maxerr=')[0],path,'exec'),env);sys.argv=old
K=env['K'];J=env['J'];layer=env['layer'];R=env['R'];H=env['H'];ya=env['ya'];I=np.eye(6)
# Real rotation chart of the Hermitian traceless octet: A=Q+i[p]_x.
a,b,c,d,e,x,y,z=s.symbols('a b c d e x y z',real=True)
Q=s.Matrix([[a,b,c],[b,d,e],[c,e,-a-d]]);p=s.Matrix([x,y,z]);X=s.Matrix([[0,-z,y],[z,0,-x],[-y,x,0]]);T=Q+s.I*X
assert T.H==T and s.trace(T)==0
assert s.expand(s.trace(T*T)-s.trace(Q*Q)-2*p.dot(p))==0
assert (T+s.conjugate(T))/2==Q and (T-s.conjugate(T))/(2*s.I)==X
assert s.Matrix(9,1,list(T)).jacobian([a,b,c,d,e,x,y,z]).rank()==8
# The actual octet-to-sheet map: scalar angular weight p.n+n^T Q n.
n=s.Matrix(s.symbols('n:3',real=True));nx=s.Matrix([[0,-n[2],n[1]],[n[2],0,-n[0]],[-n[1],n[0],0]])
B0=nx.row_join(s.eye(3)-n*n.T)
def avg(expr):
    return s.expand(sum(c*s.prod(s.factorial2(i-1) for i in k)/s.factorial2(sum(k)+1) for k,c in s.Poly(s.expand(expr),*n).terms() if all(i%2==0 for i in k)))
K8=(-Q/5).row_join(-X/2).col_join((X/2).row_join(-Q/5))
actual=(s.Rational(3,2)*(p.dot(n)+n.dot(Q*n))*B0.T*B0).applyfunc(avg)
assert actual==K8 and K8.T==K8
assert s.expand(s.trace(K8*K8)-2*s.trace(Q*Q)/25-p.dot(p))==0
assert s.Matrix(36,1,list(K8)).jacobian([a,b,c,d,e,x,y,z]).rank()==8
axis=np.ones(3)/np.sqrt(3);ka=np.array(K8.subs({a:0,b:0,c:0,d:0,e:0,x:axis[0],y:axis[1],z:axis[2]}),float)
assert np.max(abs(ka-K))<1e-14
# Equal Frobenius-norm octet directions, not equal physical material resources.
Qdir=np.outer(axis,axis)-np.eye(3)/3;Kq=np.kron(np.eye(2),-Qdir/5);Kq/=np.linalg.norm(Kq)
Km=(K+Kq)/np.sqrt(2)
# Prescribed symmetric stiffness modulation, derived energy derivative.
P=s.Matrix(s.symbols('P:2',real=True));v=s.Matrix(s.symbols('v:2',real=True));E=s.Matrix(s.symbols('E:2',real=True));k,kdot=s.symbols('k kdot',real=True);F=s.Matrix([[0,1],[1,0]])
B=4*s.eye(2)+k*F;d0=s.Rational(3,2);gamma=s.Rational(2,3)
U=(v.dot(v)+P.dot(B*P))/(2*d0)
acc=d0*E-gamma*v-B*P
assert s.expand(sum(s.diff(U,i)*j for i,j in zip(P,v))+sum(s.diff(U,i)*j for i,j in zip(v,acc))+s.diff(U,k)*kdot-E.dot(v)+gamma*v.dot(v)/d0-P.dot(F*P)*kdot/(2*d0))==0
# All frequencies signed. Offset branches avoid exact DC, commensurate branch
# keeps DC polarization and sets DC electric drive to zero (neutral short fixture).
# Real Fourier coefficients: sum P_n exp(i z_n tau), full conjugate branch.
cache={}
def radial(f):
    f=round(f,10)
    if f not in cache:
        if f<0:return tuple(x.conj() for x in radial(-f))
        mats={t:layer(f,R+H/2,R+H,1e-9,t).y[:,-1].reshape(2,2)@layer(f,R,R+H/2,0.,t).y[:,-1].reshape(2,2) for t in ('TE','TM')}
        cache[f]=tuple(np.diag(np.repeat([mats[t][i,j] for t in ('TE','TM')],3)) for i,j in ((0,0),(0,1),(1,0),(1,1)))
    return cache[f]
g=2*(I+.5*K)+J;yg=.1;drive=np.array([1,0,0,0,0,0],complex)
def ports(f,m):
    A,B,C,D=radial(f);z=f/7.83
    Ys=1j*z*1.5*np.linalg.inv((4-z*z+1j*2*z/3)*I+m*K)
    M=(I+g+Ys)@(A-B*yg)-(C-D*yg);N=D-(I+g+Ys)@B
    Z=np.linalg.solve(M,N);assert np.linalg.eigvalsh((Z+Z.conj().T)/2).min()>0
    Yload=np.linalg.inv(Z.conj().T)
    At=A-B@(yg*I+Yload);Ct=C-D@(yg*I+Yload)
    W=(I+g)@At-Ct
    return At,Ct,np.linalg.inv(W),Yload

def run(f0,m,N,source=True,comm=False):
    # stiffness 4I+m K(1+cos(tau)); tau=2pi*7.83*t.
    # commensurate source full mode, f0=0, source n=+-1; includes DC.
    ns=np.arange(-N,N+1);freq=f0+ns*7.83;zz=freq/7.83
    A=np.zeros((6*len(ns),6*len(ns)),complex);rhs=np.zeros(6*len(ns),complex);data=[]
    for i,(n,f,z) in enumerate(zip(ns,freq,zz)):
        sl=slice(6*i,6*i+6);ei=np.zeros(6,complex)
        if source and ((comm and abs(n)==1) or (not comm and n==0)):ei=drive/np.sqrt(2) if comm else drive
        diag=(4-z*z+1j*2*z/3)*I+m*K
        if abs(f)<1e-12:
            # Static polarization not dropped; DC E is specified zero; no radial DC claim.
            A[sl,sl]=diag;data.append(None)
        else:
            At,Ct,W,Yload=ports(f,m);Rtop=At@W
            A[sl,sl]=diag+1.5j*z*Rtop;rhs[sl]=3*Rtop@ei
            data.append((At,Ct,W,Yload,ei))
        if i:A[sl,slice(6*(i-1),6*i)]=m*K/2
        if i+1<len(ns):A[sl,slice(6*(i+1),6*(i+2))]=m*K/2
    p=solve(A,rhs).reshape(-1,6);vel=1j*zz[:,None]*p
    # For offset use RMS coefficients and their implicit conjugate branch;
    # commensurate uses ordinary Fourier coefficients on both signed branches.
    bp=np.zeros_like(p);bp[1:]+=1j*m/2*(p[:-1]@K.T);bp[:-1]-=1j*m/2*(p[1:]@K.T)
    pump=np.vdot(p,bp).real/(2*1.5) # time average P^T Bdot P /(2d)
    loss=(2/3)/1.5*np.vdot(vel,vel).real
    inc=ref=sheet=ground=load=rad=fieldwork=0.;side=[]
    for i,item in enumerate(data):
        if item is None:continue
        At,Ct,W,Yload,ei=item;e0=W@(2*ei-vel[i]);e1=At@e0;h1=Ct@e0;j=Yload@e0;h0=-yg*e0-j
        l=np.vdot(e0,j).real;inc+=np.vdot(ei,ei).real;ref+=np.vdot(e1-ei,e1-ei).real
        sheet+=np.vdot(e1,g@e1).real;ground+=yg*np.vdot(e0,e0).real;load+=l
        rr=np.vdot(e0,h0).real-np.vdot(e1,h1).real;assert rr>=-1e-8;rad+=rr
        fieldwork+=np.vdot(e1,vel[i]).real;side.append([float(freq[i]),float(l)])
    assert abs(fieldwork+pump-loss)<1e-8,(fieldwork,pump,loss)
    err=inc-ref+pump-sheet-ground-load-rad-loss
    assert abs(err)<1e-8
    if comm:assert np.max(abs(p-p[::-1].conj()))<1e-9
    tail=np.linalg.norm(m*K@p[0]/2)+np.linalg.norm(m*K@p[-1]/2)
    return dict(load=float(load),pump=float(pump),net=float(load-pump),incident=float(inc),reflected=float(ref),sheet=float(sheet),ground=float(ground),radial=float(rad),material=float(loss),error=float(err),tail=float(tail),dc_p=float(np.linalg.norm(p[N])) if comm else None,sidebands=side)
rows=[]
for label,control in (("dipole",K.copy()),("quadrupole",Kq),("mixed",Km)):
 K=control
 for f0,comm in ((.005,False),(.05,False),(0.,True)):
    # Same total incident energy and static surface. Compare strongest sampled
    # static stiffness mK for m in [0,2] with ideal conjugate match.
    passive=[]
    for m in np.linspace(0,2,9):
        # static solve from radial and static stiffness, no modulation.
        f=7.83 if comm else f0;At,Ct,W,Yload=ports(f,m);z=f/7.83
        Rtop=At@W;pp=np.linalg.solve((4-z*z+1j*2*z/3)*I+m*K+1.5j*z*Rtop,3*Rtop@drive)
        ee=W@(2*drive-1j*z*pp);passive.append(float(np.vdot(ee,Yload@ee).real))
    for m in (.25,.5,1.):
        a=run(f0,m,5,True,comm);b=run(f0,m,8,True,comm);off=run(f0,m,5,False,comm)
        assert max(abs(a[k]-b[k]) for k in ('load','pump','net'))<1e-7
        assert all(abs(off[k])<1e-14 for k in ('load','pump','net'))
        rows.append(dict(octet_direction=label,f0=f0,commensurate=comm,m=m,passive_best=max(passive),passive_same_mean=passive[round(m*4)],delta=b['net']-max(passive),coarse_fine=max(abs(a[k]-b[k]) for k in ('load','pump','net')),**b))
for row in rows:
    row['passive_all_directions']=max(r['passive_best'] for r in rows if r['f0']==row['f0'])
    row['delta_all_directions']=row['net']-row['passive_all_directions']
print(json.dumps(dict(status='CONDITIONAL_OCTET_PAID_FLOQUET',rows=rows,max_error=max(abs(r['error']) for r in rows),max_cutoff_difference=max(r['coarse_fine'] for r in rows),scope='Octet is constitutive chart, not eight electromagnetic channels. Prescribed stiffness modulation via ideal work port, no autonomous HF or half-mode realization. DC polarization retained with imposed E_DC=0, no static charge/field solve. Signed sidebands, finite truncation and static sampled comparator, no physical source calibration.'),indent=2))
