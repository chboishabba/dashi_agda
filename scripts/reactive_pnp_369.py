# ATTRIBUTION: This numerical implementation was assistant-authored as an illustrative
# implementation of established reactive PNP / Scharfetter-Gummel methods.
# It reuses the user's pre-existing DASHI 3x3x3 / 369 geometry. Synthetic
# three-species parameters are not source-specific BH4 evidence.
# Scientific models: Xu et al., Phys Rev E 108 064413 (2023); Herz & Knabner,
# arXiv:1605.07455 (2016). No scientific priority is asserted by this code.

"""Finite-volume 3x3x3 reactive Poisson--Nernst--Planck reference solver.

A model-specification and numerical-assay artifact, not source-calibrated BH4
kinetics or an Agda kernel theorem. Dirichlet phi=0 on all six cube faces,
blocking species boundaries, isothermal ideal dilute activities. The implicit
step checks residual, positivity and free-energy decrease before acceptance.

The 3x3x3 grid and its 54 positively oriented native bonds are EXACTLY the
existing DASHI geometry. Physical dimensions: concentrations mol/m^3; F and
RT should be supplied consistently (or nondimensionalized together).
"""
from dataclasses import dataclass
import numpy as np
from scipy.optimize import root
from scipy.special import exprel

POINTS = tuple((x,y,z) for x in (-1,0,1) for y in (-1,0,1) for z in (-1,0,1))
INDEX = {p:i for i,p in enumerate(POINTS)}
BONDS = tuple((INDEX[p], INDEX[q]) for p in POINTS
              for axis in range(3)
              if p[axis] < 1
              for q in [tuple(p[j]+(1 if axis==j else 0) for j in range(3))])
assert len(POINTS)==27 and len(BONDS)==54


@dataclass(frozen=True)
class Model:
    z: np.ndarray          # n_species valences; synthetic examples explicitly marked
    D: np.ndarray          # n_species diffusion coefficients >=0
    reactants: np.ndarray  # n_reactions x n_species nonnegative integer
    products: np.ndarray   # n_reactions x n_species nonnegative integer
    kf: np.ndarray         # n_reactions forward coefficients
    kb: np.ndarray         # n_reactions backward coefficients
    standard_mu: np.ndarray # n_species chemical standard potentials
    epsilon: float = 1.0
    RT: float = 1.0
    F: float = 1.0
    h: float = 1.0
    fixed_charge: float = 0.0

    def __post_init__(self):
        z=np.asarray(self.z,dtype=float); D=np.asarray(self.D,dtype=float)
        A=np.asarray(self.reactants); B=np.asarray(self.products)
        kf=np.asarray(self.kf,dtype=float); kb=np.asarray(self.kb,dtype=float)
        mu0=np.asarray(self.standard_mu,dtype=float)
        assert z.ndim==1 and len(z)>0 and len(D)==len(z)
        assert A.shape==B.shape and A.ndim==2 and A.shape[1]==len(z)
        assert len(kf)==len(kb)==A.shape[0] and len(mu0)==len(z)
        assert np.all(A>=0) and np.all(B>=0) and np.all(A==np.floor(A)) and np.all(B==np.floor(B))
        assert np.all(D>=0) and np.all(kf>0) and np.all(kb>0)
        assert min(self.epsilon,self.RT,self.F,self.h)>0
        nu=B-A
        if not np.allclose(nu@z,0,rtol=0,atol=1e-12):
            raise ValueError('bulk reactions violate signed charge conservation; supply electron/reservoir explicitly')
        # ln(kf/kb) = -(nu · mu0)/RT for ideal activities.
        if not np.allclose(np.log(kf/kb),-nu@mu0/self.RT,rtol=1e-10,atol=1e-12):
            raise ValueError('mass-action rates violate local thermodynamic detailed balance')


def poisson_matrix(h):
    """-Laplace with face-centered grounded Dirichlet potential; finite volume."""
    L=np.zeros((27,27))
    for i,p in enumerate(POINTS):
        for axis in range(3):
            for sign in (-1,1):
                q=list(p);q[axis]+=sign
                if q[axis] not in (-1,0,1):
                    # boundary is half a cell from cell center
                    L[i,i]+=2/h**2
                else:
                    L[i,i]+=1/h**2
                    L[i,INDEX[tuple(q)]]-=1/h**2
    return L


def poisson(c,m):
    # Solve the same self-consistent Poisson equation at EVERY step.
    rho=m.F*np.einsum('xs,s->x',c,m.z)+m.fixed_charge
    return np.linalg.solve(m.epsilon*poisson_matrix(m.h),rho)


def bernoulli(x):
    # B(x)=x/(exp(x)-1), analytically continued at x=0.
    return 1.0/exprel(x)


def native_flux(c,phi,m):
    """Exact exponential-fitting Scharfetter--Gummel native-bond flux.

    Forward orientation is a->b for each of the 54 bonds; zero at
    electrochemical equilibrium. No boundary flow is inserted here.
    """
    flux=np.empty((54,c.shape[1]))
    for e,(a,b) in enumerate(BONDS):
        du=m.z*m.F*(phi[b]-phi[a])/m.RT
        flux[e,:]=(m.D/m.h)*(c[a,:]*bernoulli(du)-c[b,:]*bernoulli(-du))
    return flux


def reaction_rates(c,m):
    # Ideal mass-action reactions, rate per volume, real nonnegative c.
    f=m.kf[None,:]*np.prod(c[:,None,:]**m.reactants[None,:,:],axis=2)
    b=m.kb[None,:]*np.prod(c[:,None,:]**m.products[None,:,:],axis=2)
    return f-b


def vector_rhs(c,m,phi=None):
    if phi is None: phi=poisson(c,m)
    dx=np.zeros_like(c)
    J=native_flux(c,phi,m)
    for e,(a,b) in enumerate(BONDS):
        # flux density -> divergence per cell volume
        dx[a,:]-=J[e,:]/m.h
        dx[b,:]+=J[e,:]/m.h
    if len(m.kf): dx+=reaction_rates(c,m)@(m.products-m.reactants)
    return dx


def free_energy(c,phi,m):
    # Grounded Dirichlet electrostatic potential (zero voltage); no external work.
    # mu0 has units of RT, and standard concentration is 1 mol/m^3.
    chemical=m.RT*np.sum(c*(np.log(c)-1))+np.sum(c*m.standard_mu[None,:])
    rho=m.F*(c@m.z)+m.fixed_charge
    electro=0.5*m.h**3*np.dot(rho,phi)
    return m.h**3*chemical+electro



def dissipation_diagnostics(c,phi,m):
    """Instantaneous transport and reaction contributions to dG/dt.

    For blocking mass boundaries and grounded potential, each is <= 0
    under the same detailed-balance constitutive law. These are physical
    numerical evaluations, NOT a discrete Agda dissipation theorem.
    """
    mu=m.standard_mu[None,:]+m.RT*np.log(c)+m.F*phi[:,None]*m.z[None,:]
    J=native_flux(c,phi,m)
    power_transport=m.h**2*sum(float(np.dot(J[e],mu[b]-mu[a]))
                               for e,(a,b) in enumerate(BONDS))
    rates=reaction_rates(c,m)
    affinity=mu@(m.products-m.reactants).T
    power_reaction=m.h**3*float(np.sum(rates*affinity))
    if power_transport>1e-9 or power_reaction>1e-9:
        raise RuntimeError('transport/reaction thermodynamic dissipation sign failed')
    return {'transport_power':float(power_transport),
            'reaction_power':float(power_reaction)}

def implicit_step(c0,dt,m,rtol=1e-8):
    """Fully coupled implicit Euler with log concentrations, checked receipt.

    This gives positivity at any converged root. Energy decreases for the
    closed isothermal detailed-balanced model when its implicit root is
    correct; failure to achieve that is a rejected numerical step.
    """
    c0=np.asarray(c0,dtype=float)
    if c0.shape!=(27,len(m.z)) or not np.all(np.isfinite(c0)) or np.any(c0<=0):
        raise ValueError('positive 27 x n source concentrations required')
    if not np.isfinite(dt) or dt<=0: raise ValueError('positive dt required')
    ph0=poisson(c0,m)
    # Use bounded exponentials only as protection from exploratory Newton
    # iterates; a converged state must solve the *unclipped* residual.
    def residual(y):
        c=np.exp(np.clip(y.reshape(c0.shape),-70,70))
        ph=poisson(c,m)
        return ((c-c0)-dt*vector_rhs(c,m,ph)).ravel()
    sol=root(residual,np.log(c0).ravel(),method='hybr',options={'xtol':1e-10})
    if not sol.success and np.max(np.abs(residual(sol.x)))>rtol:
        raise RuntimeError(f'implicit coupled PNP did not converge: {sol.message}')
    if np.any(np.abs(sol.x)>69): raise RuntimeError('log-iterate clipping invalidated root')
    c=np.exp(sol.x.reshape(c0.shape)); ph=poisson(c,m)
    defect=c-c0-dt*vector_rhs(c,m,ph)
    err=np.max(np.abs(defect))
    if err>rtol or not np.all(np.isfinite(c)):
        raise RuntimeError(f'coupled residual not paid: {err}')
    e0=free_energy(c0,ph0,m); e1=free_energy(c,ph,m)
    if e1>e0+max(1e-9,rtol*max(1,abs(e0))):
        raise RuntimeError(f'free-energy inequality failed: {e0} -> {e1}')
    charge_defect=abs(float(np.dot((c-c0).sum(axis=0),m.z)))
    if charge_defect>max(1e-9,100*rtol):
        raise RuntimeError('closed bulk total charge was not conserved')
    dissipation=dissipation_diagnostics(c,ph,m)
    return c,{**dissipation,'numerical_residual_max':float(err),'free_energy_before':float(e0),
              'free_energy_after':float(e1),'charge_defect':float(charge_defect),
              'minimum_concentration':float(c.min()),'poisson_residual_max':float(np.max(np.abs(m.epsilon*poisson_matrix(m.h)@ph-(m.F*(c@m.z)+m.fixed_charge)))),
              'model_is_source_calibrated':False,'agda_kernel_checked':False}


def synthetic_demo():
    # A+ + B- <-> C. Charge conserving, detailed balanced; all dimensionless.
    model=Model(z=np.array([1,-1,0]), D=np.array([0.12,0.1,0.08]),
        reactants=np.array([[1,1,0]]),products=np.array([[0,0,1]]),
        kf=np.array([0.04]),kb=np.array([0.04]),standard_mu=np.zeros(3))
    c=np.ones((27,3),dtype=float)
    c[:,0]=1.2;c[:,1]=1.2;c[:,2]=0.4
    c[INDEX[(-1,0,0)],0]+=0.4
    c[INDEX[(1,0,0)],1]+=0.3
    out,receipt=implicit_step(c,0.08,model)
    assert receipt['free_energy_after']<=receipt['free_energy_before']
    assert receipt['minimum_concentration']>0
    assert receipt['numerical_residual_max']<1e-8
    # Thermodynamic incompatibility is rejected, not silently 'fixed'.
    try:
        Model(z=np.array([1,-1,0]),D=np.ones(3),reactants=np.array([[1,1,0]]),
              products=np.array([[0,0,1]]),kf=np.array([2.0]),kb=np.array([1.0]),standard_mu=np.zeros(3))
    except ValueError:pass
    else:raise AssertionError('accepted detailed-balance violation')
    return receipt


if __name__=='__main__':
    import json
    print(json.dumps(synthetic_demo(),indent=2,sort_keys=True))