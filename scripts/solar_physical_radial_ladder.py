"""Energy-normalized radial l=1 TE/TM ladder from Maxwell radial equations.
Voltage/current boundary is a harmonic projection, not a spatially localized
3D interface. Keep this producer distinct from an admitted physical cone mesh.
"""
import numpy as np
from scipy.constants import epsilon_0, mu_0
from scipy.linalg import solve
from solar_periodic_radial_weld import R,H,ya
from solar_physical_periodic import shell,dc_port

def build(cells, sigma, ground):
    """Staggered radial finite volumes, boundary voltage input.
    TE: shunt magnetic inductance; TM: series radial electric relaxation.
    Orientation from outer to inner; six l=1 polarization channels.
    State energy = half squared norm. Boundary port e=r E_t.
    """
    if cells<2 or cells%2 or sigma<0 or ground<=0:
        raise ValueError('even radial cells, passive coefficients required')
    dr=H/cells
    radii=R+H-(np.arange(cells)+.5)*dr
    sg=np.where(radii>R+H/2,sigma,0.)
    dim=18*cells
    J=np.zeros((dim,dim)); Rg=np.zeros_like(J); Ro=np.zeros_like(J)
    B=np.zeros((dim,6))
    def link(i,j,a):
        J[i,j]+=a; J[j,i]-=a
    for mode in range(6):
        base=3*cells*mode
        # Series magnetic current at outer face; tangential electric
        # voltage at cell centre; longitudinal auxiliary at centre.
        for i,r in enumerate(radii):
            h=base+3*i; v=h+1; u=h+2
            rate=1/(dr*np.sqrt(mu_0*epsilon_0))
            link(h,v,-rate)
            if i==0: B[h,mode]=1/np.sqrt(mu_0*dr)
            else: link(h,v-3,rate)
            angular=np.sqrt(2)/(r*np.sqrt(mu_0*epsilon_0))
            if mode<3:
                link(v,u,-angular)
            else:
                link(h,u,-angular)
                Ro[u,u]=sg[i]/epsilon_0
            Ro[v,v]=sg[i]/epsilon_0
        # Resistive terminating boundary. Tangential voltage at last node
        # drives ground current with conductance ya*ground.
        Rg[base+3*(cells-1)+1,base+3*(cells-1)+1]=ya*ground/(epsilon_0*dr)
    return dict(J_s_inv=J.tolist(),B=B.tolist(),R_ground_s_inv=Rg.tolist(),
                R_other_s_inv=Ro.tolist(),D_ground_S=np.zeros((6,6)).tolist(),
                D_other_S=np.zeros((6,6)).tolist()),radii

def static_magnetic(radii,permeability,outer_potential):
    """l=1 magnetic scalar potential: phi=a*r+b/r².
    Regular interior, continuity of phi and radial B; prescribed outer phi.
    Static energy is stored, not useful resistive work.
    """
    r=np.asarray(radii,float); mu=np.asarray(permeability,float)
    if len(r)!=len(mu) or np.any(r<=0) or np.any(np.diff(r)<=0) or np.any(mu<=0):
        raise ValueError('ordered positive outer radii and permeabilities')
    def chart(x,m):
        return np.array([[x,x**-2],[-m,2*m/x**3]])
    coeff=[np.array([1.,0.])]
    for i,x in enumerate(r[:-1]):
        coeff.append(solve(chart(x,mu[i+1]),chart(x,mu[i])@coeff[-1]))
    scale=outer_potential/(chart(r[-1],mu[-1])@coeff[-1])[0]
    coeff=np.array(coeff)*scale
    # Angular basis unit integral; grad energy radial integrand
    # mu*(r² phi'²+2 phi²)/2, cross terms cancel.
    energy=0.
    for i,(a,b) in enumerate(coeff):
        lo=0. if i==0 else r[i-1]; hi=r[i]
        energy+=mu[i]/2*(a*a*(hi**3-lo**3)+(2*b*b*(lo**-3-hi**-3) if lo else 0.))
    return dict(coefficients=coeff.tolist(),stored_J=float(energy),ground_work_J=0.)

def audit(cfg,cells,frequencies):
    from solar_physical_causal import Shell
    spec,radii=build(cells,cfg['shell_sigma_S_m'],cfg['ground_admittance_normalized'])
    sh=Shell(spec); rows=[]
    for f in frequencies:
        if f==0: continue # static constraints, not invert singular conserved modes
        y,g=shell(f,cfg['ground_admittance_normalized'],cfg['shell_sigma_S_m'],*dc_port(cfg))
        Z=sh.admittance(f); T=solve(2j*np.pi*f*np.eye(len(sh.J))-sh.J+sh.R,sh.B)
        ground=T.conj().T@sh.Rg@T
        rows.append(dict(f_Hz=f,admittance_relative_error=float(np.linalg.norm(Z-np.diag(y))/max(np.linalg.norm(y),1e-30)),
                         ground_relative_error=float(np.linalg.norm(ground-np.diag(abs(g)**2))/max(np.linalg.norm(abs(g)**2),1e-30))))
    return dict(cells=cells,radial_centres_m=radii.tolist(),rows=rows,physical_cone_admitted=False)

if __name__=='__main__':
    import json
    cfg=dict(shell_sigma_S_m=1e-9,ground_admittance_normalized=1.,
             dc_admittance_S=[0.]*6,dc_ground_transfer_sqrt_S=[0.]*6)
    print(json.dumps(dict(radial=[audit(cfg,n,[3.915,7.83,15.66]) for n in (4,8,16)],
      static=static_magnetic([R,R+H],[mu_0,mu_0],1.)),indent=2))
