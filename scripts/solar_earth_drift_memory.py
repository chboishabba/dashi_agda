"""Original row-wise drift fibres and cold-fluid memory; no fitted wind or E field."""
import hashlib,json,sys
from pathlib import Path
import h5py
import numpy as np
import sympy as s
from scipy.constants import atomic_mass as u
from scipy.linalg import expm
from solar_earth_model_inputs import radar
from solar_earth_collision_tensor import composition,rates

def exact_checks():
    m,n,nu,S,R,p,div=s.symbols('m n nu S R p div',positive=True)
    v,w,b,E,B,g=s.symbols('v w b E B g',real=True),None,None,None,None,None
    v,w,b,E,B,g=[s.Matrix(s.symbols(f'{x}:3',real=True)) for x in ('v','w','b','E','B','g')]
    q=s.symbols('q',real=True,nonzero=True); j=n*q*v; d=v-w
    # Material derivative of n: continuity includes expansion and population exchange.
    ndot=S-R-n*div
    vd=q*(E+v.cross(B))/m-nu*d-g/(m*n)+S*(b-v)/n
    K=m*n*v.dot(v)/2
    kd=m*ndot*v.dot(v)/2+m*n*v.dot(vd)+K*div
    rhs=j.dot(E)-v.dot(g)-m*n*nu*(d.dot(d)+w.dot(d))+m*S*b.dot(b)/2-m*S*(b-v).dot(b-v)/2-m*R*v.dot(v)/2
    assert s.expand(kd-rhs)==0
    # Pressure work becomes boundary flux plus internal-energy transfer.
    assert s.expand(-v.dot(g)-(-(v.dot(g)+p*div)+p*div))==0
    # Difference equation for two histories with same prescribed inputs/population.
    delta=s.Matrix(s.symbols('z:3',real=True))
    assert s.expand(delta.dot(q*delta.cross(B)/m-(nu+S/n)*delta)+(nu+S/n)*delta.dot(delta))==0
    # Current-density difference in a homogeneous fixed cell (div=0).
    assert s.expand(delta.dot(q*delta.cross(B)/m-(nu+R/n)*delta)+(nu+R/n)*delta.dot(delta))==0
    return 4

def main(root,packet):
    checks=exact_checks(); rows=radar(root); raw=packet.read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='d771b81b3498e4cf9424325afe9e27f1c3f8125d0ba6c608c175cb62bd955fb6'
    model=[json.loads(x) for x in raw.splitlines()]; assert len(model)==len(rows)==3087
    for r,x in zip(rows,model): assert all(r[k]==x[k] for k in ('record','range_km','utc'))
    with h5py.File(root/'MAD6400_2017-12-18_bella_60@vhf.hdf5') as f: a=f['Data/Table Layout'][:]
    key={(int(x['recno']),float(x['range'])):x for x in a}; a=np.array([key[r['record'],r['range_km']] for r in rows]); y=a['vo'].astype(float); dur=a['ut2_unix']-a['ut1_unix']
    # Transport station ENU ray into each row's own right-handed NED frame.
    def frame(lat,lon):
        lat,lon=np.radians(lat),np.radians(lon)
        return np.stack([[-np.sin(lat)*np.cos(lon),-np.sin(lat)*np.sin(lon),np.cos(lat)],[-np.sin(lon),np.cos(lon),0],[-np.cos(lat)*np.cos(lon),-np.cos(lat)*np.sin(lon),-np.sin(lat)]])
    az,el=np.radians([a['azm'][0],a['elm'][0]]); ray=frame(69.6,19.2).T@np.array([np.cos(el)*np.cos(az),np.cos(el)*np.sin(az),-np.sin(el)])
    r=np.array([frame(x['lat'],x['lon'])@ray for x in rows]); B=np.array([x['B_NED_T'] for x in model]); b=B/np.linalg.norm(B,axis=1)[:,None]
    proj=r-(r*b).sum(axis=1)[:,None]*b; g=(proj*proj).sum(axis=1); assert np.all(g>0) and np.all(g<=1+1e-14)
    v0=y[:,None]*r; vp=y[:,None]*proj/g[:,None]; z=np.cross(b,r); z/=np.linalg.norm(z,axis=1)[:,None]; alt=vp+z
    assert np.allclose((vp*r).sum(axis=1),y) and np.allclose((vp*b).sum(axis=1),0,atol=1e-12)
    assert np.allclose((alt*r).sum(axis=1),y) and np.allclose((alt*b).sum(axis=1),0,atol=1e-12)
    assert np.allclose((alt*alt).sum(axis=1)-(vp*vp).sum(axis=1),1,atol=1e-9)
    # If wind is unrestricted, choosing wind=v0 makes relative drift zero.
    fractions=composition(root,rows); ne=np.array([x['ne'] for x in rows]); mass=u*np.array([30.5,16.]); quant=lambda x:np.quantile(x,[0,.5,1],axis=0).tolist(); out={}
    for label in ('history','daily'):
        nu=rates(rows,np.array([x['neutral_'+label+'_SI'] for x in model])); drag=ne*np.sum(fractions*mass*nu[:,1:],axis=1)
        # Common ion velocity, zero wind and pointwise LOS: these are proxy minima, not measured heating.
        free=drag*y*y; perp=free/g
        assert np.all(perp>=free*(1-1e-13))
        out[label]={'zero_wind_los_min_W_m3':quant(free),'zero_wind_perp_min_W_m3':quant(perp),'ion_drag_kg_m3_s':quant(drag),'frozen_e_fold_s':quant(1/nu),'frozen_log10_memory_over_integration':quant(-nu*dur[:,None]/np.log(10))}
    # Numerical independent checks of the skew+drag transition, on dimensionless fixtures only.
    ncheck=0
    for omega in (-11.,0.,7.):
        for nu in (0.,.25,2.):
            for h in (.01,.2,1.):
                J=np.array([[0.,-1,0],[1,0,0],[0,0,0]]); A=-nu*np.eye(3)-omega*J; T=expm(h*A)
                assert np.allclose(T.T@T,np.exp(-2*nu*h)*np.eye(3),rtol=1e-12,atol=1e-13); ncheck+=1
    print(json.dumps({'status':'CONDITIONAL_DRIFT_FIBRE_AND_MEMORY','rows':len(rows),'records':len(set(x['record'] for x in rows)),'packet_sha256':hashlib.sha256(raw).hexdigest(),'beam_B_parallel_cosine':quant((r*b).sum(axis=1)),'perp_projection_squared':quant(g),'perp_minimum_multiplier':quant(1/g),'unconstrained_pointwise_nullity':2,'perp_constraint_pointwise_nullity':1,'unrestricted_wind_lower_bound_W_m3':0,'histories':out,'symbolic_identities':checks,'matrix_exponential_fixtures':ncheck,'physical_admission':False,'scope':'Common ion drift, selected alternative collision law and main field, conditional zero-wind minima; radar integration averages not instantaneous velocities. No wind or E field inference, no spatial heating integral. Frozen-rate memory diagnostic, not a measured history.'},indent=2))
if __name__=='__main__':main(Path(sys.argv[1]),Path(sys.argv[2]))
