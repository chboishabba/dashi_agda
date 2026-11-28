"""Indexed 1D staggered Maxwell/Drude split transport, conditional finite model.
The grid, boundary traces and sources must be supplied; radar rows are not a mesh.
"""
import hashlib
import json
import sys
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import expm
from scipy.constants import epsilon_0, mu_0, elementary_charge as e, electron_mass as me, atomic_mass as u
from solar_earth_coupled_cell import generator, maps
from solar_earth_retarded_current import radar, rates, composition

J = np.array([[0., -1.], [1., 0.]])

class Grid:
    """E (three components) at cells, H (two) at interior or periodic faces.
    State normalized by sqrt(dx * energy weight). Boundary H is prescribed.
    """
    def __init__(self, dx, cells, mu, periodic=False):
        self.dx=float(dx); self.n=len(cells); self.periodic=bool(periodic)
        self.eps=np.array([q['eps'] for q in cells],float)
        nf=self.n if periodic else self.n-1
        self.mu=np.broadcast_to(np.asarray(mu,float),(nf,)).copy()
        if self.n<2 or not np.isfinite(self.dx) or self.dx<=0 or np.any(~np.isfinite(self.mu)) or np.any(self.mu<=0):
            raise ValueError('invalid grid')
        self.local=[]; offset=0
        for q in cells:
            A,R,_=generator(q['D'],q['nu'],q['omega'],q['b'],q['eps'],q.get('load',0.))
            self.local.append((slice(offset,offset+len(A)),A,R)); offset+=len(A)
        self.faces=[]; self.edges=[]
        for f in range(nf):
            left,right=f,(f+1)%self.n
            hs=slice(offset+2*f,offset+2*f+2); self.faces.append(hs)
            for i,sign in ((left,1),(right,-1)):
                es=self.local[i][0]; scale=sign/(self.dx*np.sqrt(self.eps[i]*self.mu[f]))
                for a,b in ((0,1),(1,0)):
                    self.edges.append((f,i,es.start+a,hs.start+b,scale*J[a,b]))
        self.size=offset+2*nf

    def boundary_vector(self,left,right):
        left,right=np.asarray(left,float),np.asarray(right,float)
        if left.shape!=(2,) or right.shape!=(2,) or not np.isfinite([*left,*right]).all(): raise ValueError('boundary H vectors')
        if self.periodic and (np.any(left) or np.any(right)): raise ValueError('no exterior faces on periodic grid')
        v=np.zeros(self.size)
        for i,H,sign in ((0,left,-1),(self.n-1,right,1)):
            start=self.local[i][0].start
            v[start:start+2]=sign*(J@H)/np.sqrt(self.dx*self.eps[i])
        return v

    def dense(self):
        A=np.zeros((self.size,self.size)); C=A.copy()
        for sl,a,_ in self.local: A[sl,sl]=a
        for _,_,i,j,k in self.edges: C[i,j]+=k; C[j,i]-=k
        return A+C,C

    def prepare(self,h):
        if not np.isfinite(h) or h<=0: raise ValueError('positive time')
        return self,h,[maps(A,R,h) for _,A,R in self.local]

    def step(self,z,h,prepared,left=(0,0),right=(0,0),controller=None):
        owner,ph,local_maps=prepared
        if owner is not self or ph!=h or len(local_maps)!=self.n: raise ValueError('prepared timestep mismatch')
        z=np.array(z,float,copy=True)
        if z.shape!=(self.size,) or not np.isfinite(z).all(): raise ValueError('state')
        leftv=self.boundary_vector(left,(0,0)); rightv=self.boundary_vector((0,0),right)
        ctrl=np.zeros(self.size) if controller is None else np.asarray(controller,float)
        electric={i for sl,_,_ in self.local for i in range(sl.start,sl.start+3)}
        if ctrl.shape!=(self.size,) or not np.isfinite(ctrl).all() or any(ctrl[i]!=0 for i in range(self.size) if i not in electric): raise ValueError('controller electric drive only')
        work=np.zeros((3,self.n)); transfers=np.zeros((len(self.faces),self.n)); loss=np.zeros(self.n); load=loss.copy()
        kicks=(leftv,rightv,ctrl); material_inputs=[]
        def kick(i):
            delta=h/2*kicks[i]
            for cell,(sl,_,_) in enumerate(self.local): work[i,cell]+=delta[sl]@(z[sl]+delta[sl]/2)
            z[:]+=delta
        def edge(q):
            f,cell,i,j,k=q; t=h*k/4; c=(1-t*t)/(1+t*t); sn=2*t/(1+t*t)
            x,y=z[i],z[j]; z[i]=c*x+sn*y; z[j]=-sn*x+c*y
            # Energy into electric cell from this indexed magnetic face.
            transfers[f,cell]+=(z[i]**2-x*x)/2
        for i in range(3): kick(i)
        for q in self.edges: edge(q)
        for cell,((sl,_,_), (T,Q)) in enumerate(zip(self.local,local_maps)):
            v=z[sl].copy(); material_inputs.append(v); load[cell]=v@Q[0]@v; loss[cell]=sum(v@q@v for q in Q[1:]); z[sl]=T@v
        for q in reversed(self.edges): edge(q)
        for i in reversed(range(3)): kick(i)
        return z,dict(exterior_inward=work[:2].sum(axis=1),controller=work[2].sum(),cell_source_work=work.sum(axis=0),face_to_cell=transfers,material_loss=loss,load=load,material_inputs=tuple(material_inputs))


def verify_step(grid,z,h,p,left=(0,0),right=(0,0),controller=None):
    v,w=grid.step(z,h,p,left,right,controller)
    residual=(v@v-z@z)/2+w['material_loss'].sum()+w['load'].sum()-w['exterior_inward'].sum()-w['controller']
    face_error=max(abs((v[sl]@v[sl]-z[sl]@z[sl])/2+w['face_to_cell'][i].sum()) for i,sl in enumerate(grid.faces))
    cell_error=max(abs((v[sl]@v[sl]-z[sl]@z[sl])/2+w['material_loss'][i]+w['load'][i]-w['face_to_cell'][:,i].sum()-w['cell_source_work'][i]) for i,(sl,_,_) in enumerate(grid.local))
    assert max(abs(residual),face_error,cell_error)<1e-10
    return v,w,max(abs(residual),face_error,cell_error)


def cell(eps=1.,D=(0.,),nu=(0.,),omega=(0.,),load=0.):
    return dict(eps=eps,D=D,nu=nu,omega=omega,b=np.array([2.,-1.,2.])/3,load=load)


def fixtures():
    t=s.symbols('t',real=True); c=(1-t*t)/(1+t*t); sn=2*t/(1+t*t); U=s.Matrix([[c,sn],[-sn,c]])
    assert (U.T*U-s.eye(2)).applyfunc(s.cancel)==s.zeros(2)
    # Heterogeneous passive and forced case, independent dense affine reference.
    grid=Grid(.7,[cell(1.,(2.,),(.4,),(-3.,)),cell(2.,(1.,0.),(.2,.5),(2.,4.),.3),cell(1.5)], [1.2,.8])
    A,C=grid.dense(); assert np.array_equal(C+C.T,np.zeros_like(C))
    z=np.linspace(-.2,.4,grid.size); left=(.3,-.2); right=(-.1,.4); ctrl=np.zeros(grid.size); ctrl[2]=.2
    force=grid.boundary_vector(left,right)+ctrl; M=np.zeros((grid.size+1,grid.size+1)); M[:-1,:-1]=A; M[:-1,-1]=force
    end=.8; ref=(expm(end*M)@np.r_[z,1.])[:-1]; errs=[]; ledger=0.; negative=False
    for n in (8,16,32,64):
        h=end/n; p=grid.prepare(h); x=z.copy()
        for _ in range(n):
            x,w,r=verify_step(grid,x,h,p,left,right,ctrl); ledger=max(ledger,r); negative|=bool(np.any(w['exterior_inward']<0))
        errs.append(float(np.linalg.norm(x-ref)))
    orders=np.log2(np.array(errs[:-1])/errs[1:]); assert np.min(orders)>1.9 and negative
    try: grid.step(z,.2,grid.prepare(.1))
    except ValueError: pass
    else: raise AssertionError('stale prepared map accepted')
    # One-step dependency graph is a numerical stage cone, not a physical cone.
    g=Grid(1.,[cell() for _ in range(8)],1.); z=np.zeros(g.size); z[0]=1.; reached={0}
    for f,i,a,b,k in g.edges+list(reversed(g.edges)):
        if reached.intersection((a,b)): reached.update((a,b))
    x,_,r=verify_step(g,z,.1,g.prepare(.1)); assert all(x[i]==0 for i in range(g.size) if i not in reached)
    # Vacuum staggered Fourier dispersion, independent of temporal splitting.
    dispersion=[]
    for n in (8,16,32,64):
        g=Grid(1/n,[cell() for _ in range(n)],1.,periodic=True); A,_=g.dense()
        k=2*np.pi; dx=1/n; z=np.zeros(g.size,complex)
        for i,(sl,_,_) in enumerate(g.local): z[sl.start]=np.exp(1j*k*i*dx)
        for i,sl in enumerate(g.faces): z[sl.start+1]=np.exp(1j*k*(i+.5)*dx)
        omega=2*np.sin(k*dx/2)/dx
        assert np.linalg.norm(A@z+1j*omega*z)/np.linalg.norm(z)<1e-12
        dispersion.append(abs(k-omega))
    spatial_orders=np.log2(np.array(dispersion[:-1])/dispersion[1:]); assert np.min(spatial_orders)>1.9
    return dict(temporal_errors=errs,temporal_orders=orders.tolist(),vacuum_dispersion_errors=dispersion,vacuum_spatial_orders=spatial_orders.tolist(),max_ledger_residual=ledger,negative_boundary_control=negative,cone_reached=len(reached),cone_total=len(x),symbolic_rotation=True)


def model_fixtures(root,packet):
    raw=packet.read_bytes(); digest=hashlib.sha256(raw).hexdigest(); assert digest=='d771b81b3498e4cf9424325afe9e27f1c3f8125d0ba6c608c175cb62bd955fb6'
    rows=radar(root); model=[json.loads(x) for x in raw.splitlines()]; assert len(model)==len(rows)==3087
    for r,m in zip(rows,model): assert all(r[k]==m[k] for k in ('record','range_km','utc'))
    fractions=composition(root,rows); mass=np.array([me,30.5*u,16*u]); charge=e*np.array([-1,1,1]); worst=0.; count=0
    # Independent uniform trial grids, each uses ONE actual model row. No inferred spatial arrangement.
    ids=np.linspace(0,len(rows)-1,9,dtype=int)
    for label in ('history','daily'):
        nu=rates(rows,np.array([m['neutral_'+label+'_SI'] for m in model]))
        for i in ids:
            B=np.array(model[i]['B_NED_T']); mag=np.linalg.norm(B); D=rows[i]['ne']*np.r_[1.,fractions[i]]*charge**2/mass
            q=dict(eps=epsilon_0,D=D,nu=nu[i],omega=mag*charge/mass,b=B/mag)
            g=Grid(100.,[q]*3,mu_0); z=np.linspace(-.1,.1,g.size); h=1e-8
            for _ in range(4): z,_,res=verify_step(g,z,h,g.prepare(h)); worst=max(worst,res); count+=1
    return dict(packet_sha256=digest,model_rows=len(ids),uniform_trial_grids=2*len(ids),model_steps=count,max_model_ledger_residual=worst)

if __name__=='__main__':
    out=fixtures(); out.update(model_fixtures(Path(sys.argv[1]),Path(sys.argv[2]))); out.update(status='CONDITIONAL_STAGGERED_SPATIAL_TRANSPORT',physical_admission=False,scope='1D finite staggered cochain model, prescribed signed boundary H and electric drives; no calibrated mesh, exterior radiation/ground solution, physical light-cone or measured source.')
    print(json.dumps(out,indent=2))
