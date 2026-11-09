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
        if z.ndim!=1 or len(z)==0 or D.shape!=z.shape or mu0.shape!=z.shape:
            raise ValueError('species, diffusivity and chemical potentials require common 1D dimensions')
        if A.ndim!=2 or B.shape!=A.shape or A.shape[1]!=len(z):
            raise ValueError('gross source reaction sides must be matching 2D species matrices')
        if kf.shape!=(A.shape[0],) or kb.shape!=(A.shape[0],):
            raise ValueError('each reaction needs a forward and reverse rate')
        if not (np.all(np.isfinite(z)) and np.all(np.isfinite(D))
                and np.all(np.isfinite(mu0)) and np.all(np.isfinite(kf))
                and np.all(np.isfinite(kb)) and np.all(np.isfinite(A))
                and np.all(np.isfinite(B))):
            raise ValueError('nonfinite PNP species, rate or reaction parameter')
        if not (np.all(A>=0) and np.all(B>=0)
                and np.all(A==np.floor(A)) and np.all(B==np.floor(B))):
            raise ValueError('gross reaction orders must be nonnegative integers')
        if not (np.all(D>=0) and np.all(kf>0) and np.all(kb>0)):
            raise ValueError('diffusion and reaction parameters violate sign domain')
        physics=(self.epsilon,self.RT,self.F,self.h,self.fixed_charge)
        if not all(np.isfinite(p) for p in physics) or not all(p>0 for p in physics[:4]):
            raise ValueError('finite positive electrostatic/thermal/mesh scales required')
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



def original_grounded_poisson_coercivity_certificate():
    """Exact integer SOS identity for the original 27-cell Dirichlet operator.

    For unit h: 2*L = 6*I + sum_{27 native axis lines}
       [v_minus*v_minus.T + v_plus*v_plus.T],
    with v_minus = 2 e_minus - e_zero and v_plus = 2 e_plus - e_zero.
    All entries are integers; this is not a floating-point eigentest.
    For h,eps>0 this algebraically yields L_h >= 3/h^2 I,
    eps*L_h SPD, unique Poisson solution and inverse norm <=h^2/(3eps).
    The sharp equality mode is (1,2,1) tensor (1,2,1) tensor (1,2,1).
    """
    L = np.zeros((27,27), dtype=np.int64)
    boundary_faces = 0
    for i,p in enumerate(POINTS):
        for axis in range(3):
            for sign in (-1,1):
                q=list(p);q[axis]+=sign
                if q[axis] not in (-1,0,1):
                    L[i,i] += 2
                    boundary_faces += 1
                else:
                    L[i,i] += 1
                    L[i,INDEX[tuple(q)]] -= 1
    sos = np.zeros((27,27), dtype=np.int64)
    lines = 0
    for axis in range(3):
        for cross in ((a,b) for a in (-1,0,1) for b in (-1,0,1)):
            endpoints=[]
            for position in (-1,0,1):
                site=list(cross)
                site.insert(axis,position)
                endpoints.append(INDEX[tuple(site)])
            for end in (0,2):
                v=np.zeros(27,dtype=np.int64)
                v[endpoints[end]]=2
                v[endpoints[1]]=-1
                sos += np.outer(v,v)
            lines += 1
    if boundary_faces != 54 or lines != 27:
        raise RuntimeError('native grounded cubical geometry mismatch')
    if not np.array_equal(2*L,6*np.eye(27,dtype=np.int64)+sos):
        raise RuntimeError('exact grounded Poisson sum-of-squares identity failed')
    sharp=np.array([
        np.prod([2 if coordinate == 0 else 1 for coordinate in site])
        for site in POINTS
    ],dtype=np.int64)
    if not np.array_equal(L@sharp,3*sharp):
        raise RuntimeError('sharp grounded Poisson equality mode mismatch')
    return {
        'native_points':27, 'native_bonds':54, 'exterior_half_faces':54,
        'native_axis_lines':27,
        'exact_integer_matrix_identity':True,
        'sharp_unit_mesh_eigenvalue':3,
        'sharp_mode':sharp.tolist(),
        'coercivity_constant':'3 * epsilon / h^2',
        'inverse_norm_bound':'h^2 / (3 * epsilon)',
        'scope':'constant-positive-permittivity, all-six-face grounded Dirichlet',
        'discrete_finite_linear_poisson_only':True,
        'coupled_implicit_pnp_existence_proved':False,
        'agda_kernel_checked':False,
    }

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
    if not np.isfinite(power_transport) or not np.isfinite(power_reaction):
        raise RuntimeError('nonfinite transport/reaction power')
    if power_transport>1e-9 or power_reaction>1e-9:
        raise RuntimeError('transport/reaction thermodynamic dissipation sign failed')
    return {'transport_power':float(power_transport),
            'reaction_power':float(power_reaction)}


def closed_pnp_entropy_factorization(c,phi,m):
    """Independent numerical assay of the exact closed-system entropy signs.

    The *mathematical* factorization uses B(-u)=exp(u)B(u):
      J_ab*(mu_b-mu_a)
       = -(D*RT/h)*(q_left-q_right)*log(q_left/q_right),
      q_left=c_a B(u), q_right=c_b B(-u), both strictly positive.
    Detailed balance plus nu.z=0 similarly gives
      reaction_rate * (nu.mu) = -RT*(f-b)*log(f/b).
    Since (a-b)(log(a)-log(b))>=0 for a,b>0, each term <=0.
    This function checks the factorization for finite positive input;
    the proof is algebraic and does not rely on random samples.
    """
    c=np.asarray(c,dtype=float)
    phi=np.asarray(phi,dtype=float)
    if c.shape!=(27,len(m.z)) or phi.shape!=(27,) or (
        not np.all(np.isfinite(c)) or not np.all(np.isfinite(phi))
        or np.any(c<=0)):
        raise ValueError("positive finite native PNP state/potential required")
    mu=m.standard_mu[None,:]+m.RT*np.log(c)+m.F*phi[:,None]*m.z[None,:]
    J=native_flux(c,phi,m)
    per_bond=[]
    for edge,(a,b) in enumerate(BONDS):
        u=m.z*m.F*(phi[b]-phi[a])/m.RT
        left=c[a]*bernoulli(u)
        right=c[b]*bernoulli(-u)
        if not (np.all(np.isfinite(left)) and np.all(np.isfinite(right))
                and np.all(left>0) and np.all(right>0)):
            raise ValueError("nonpositive/nonfinite original SG Bernoulli weights")
        exact_form=-(m.D*m.RT/m.h)*(left-right)*(np.log(left)-np.log(right))
        actual=J[edge]*(mu[b]-mu[a])
        if not np.allclose(exact_form,actual,rtol=1e-9,atol=1e-10):
            raise RuntimeError("source PNP SG entropy factorization mismatch")
        per_bond.append(float(np.sum(actual)*m.h**2))
    nu=m.products-m.reactants
    forward=m.kf[None,:]*np.prod(c[:,None,:]**m.reactants[None,:,:],axis=2)
    backward=m.kb[None,:]*np.prod(c[:,None,:]**m.products[None,:,:],axis=2)
    if not (np.all(np.isfinite(forward)) and np.all(np.isfinite(backward))
            and np.all(forward>0) and np.all(backward>0)):
        raise ValueError("positive finite reaction activities required")
    exact_reaction=-m.RT*(forward-backward)*(np.log(forward)-np.log(backward))
    actual_reaction=(forward-backward)*(mu@nu.T)
    if not np.allclose(exact_reaction,actual_reaction,rtol=1e-9,atol=1e-10):
        raise RuntimeError("source PNP detailed-balanced entropy factorization mismatch")
    if np.any(exact_reaction>1e-9):
        raise RuntimeError("reaction entropy inequality violated")
    total_reaction=float(np.sum(actual_reaction)*m.h**3)
    total_transport=float(np.sum(per_bond))
    if total_reaction>1e-9 or total_transport>1e-9:
        raise RuntimeError("source PNP closed entropy production violated")
    return {
        "bond_terms": len(per_bond),
        "reaction_terms": int(actual_reaction.size),
        "transport_power": total_transport,
        "reaction_power": total_reaction,
        "exact_analytic_hypotheses":
            "positive concentrations, positive RT/h, nonnegative diffusion, "
            "charge-neutral bulk stoichiometry, detailed-balanced positive rates",
        "finite_numerical_factorization_checked": True,
        "general_implicit_positive_root_existence_proved": False,
        "agda_kernel_checked": False,
    }



def local_positive_implicit_contraction_bounds(c0,m):
    """Explicit sufficient *small-dt* contractivity bounds for native PNP.

    If c0>0, r=min(c0)/2, Q=max(c0)+r and
       dt*M <= r, dt*L < 1,
    then T(c)=c0+dt*vector_rhs(c,m,poisson(c,m)) maps the closed
    sup-norm ball B_infty(c0,r) into itself and is a contraction.
    Hence Banach yields exactly one strictly positive implicit root in
    this ball; c>=r. This is a finite analytical existence theorem
    conditional on these explicit source-parameter inequalities. It is
    NOT a universal timestep claim, nor an Agda kernel proof.

    Derivation:
    epsilon L_h >=3epsilon/h² in l2 gives
      ||phi||_inf <=h² sqrt(27)/(3epsilon)*||rho||_inf
      Lip_inf(phi) <=h² sqrt(27) F sum|z|/(3epsilon).
    The Bernoulli function is positive, B(u)<=1+|u|,
    and globally 1-Lipschitz since -1<=B'(u)<=0.
    Six incident native bonds bound every voxel divergence.
    Product telescoping bounds reversible mass action on [0,Q].
    """
    c0=np.asarray(c0,dtype=float)
    if c0.shape!=(27,len(m.z)) or not np.all(np.isfinite(c0)) or np.any(c0<=0):
        raise ValueError("positive finite full 27-species field required")
    r=float(c0.min())/2.0
    Q=float(c0.max())+r
    z=np.asarray(m.z,dtype=float)
    D=np.asarray(m.D,dtype=float)
    nu=np.asarray(m.products-m.reactants,dtype=float)
    A=np.asarray(m.reactants,dtype=float)
    B=np.asarray(m.products,dtype=float)
    Acount=A.sum(axis=1)
    Bcount=B.sum(axis=1)
    Qstar=max(1.0,Q)
    geometric=m.h**2*np.sqrt(27.0)/(3.0*m.epsilon)
    phi_bound=geometric*(m.F*np.sum(np.abs(z))*Q+abs(m.fixed_charge))
    phi_lipschitz=geometric*m.F*np.sum(np.abs(z))
    u_bound=2.0*np.max(np.abs(z))*m.F*phi_bound/m.RT
    bmax=1.0+u_bound
    u_lipschitz=2.0*np.abs(z)*m.F*phi_lipschitz/m.RT
    # On [0,Q], |prod(x_i^a_i)|<=Qstar^sum a.
    # Mean-value/product telescoping bound:
    # Lip_inf(prod x_i^a_i)<=sum(a_i)*Qstar^sum(a_i).
    forward_envelope=np.asarray(m.kf)*Qstar**Acount
    backward_envelope=np.asarray(m.kb)*Qstar**Bcount
    reaction_amplitude=np.abs(nu).T@(forward_envelope+backward_envelope)
    reaction_lipschitz=np.abs(nu).T@(
        forward_envelope*Acount+backward_envelope*Bcount)
    transport_amplitude=12.0*D*Q*bmax/m.h**2
    transport_lipschitz=12.0*D*(bmax+Q*u_lipschitz)/m.h**2
    M=float(np.max(transport_amplitude+reaction_amplitude))
    L=float(np.max(transport_lipschitz+reaction_lipschitz))
    if not np.all(np.isfinite([r,Q,phi_bound,phi_lipschitz,u_bound,bmax,M,L])):
        raise ValueError("nonfinite analytic majorant: physical scales too extreme")
    if r<=0 or M<0 or L<0:
        raise ValueError("invalid strict positive-ball bounds")
    # Conservative sufficient interval avoids floating-point strictness
    # ambiguities at the mathematical endpoints:
    # dt <= r/(2M) and dt <=1/(2L), for M,L positive.
    dt_upper=min(r/(2*M) if M>0 else np.inf,
                 1/(2*L) if L>0 else np.inf)
    if not np.isfinite(dt_upper) or dt_upper<=0:
        raise ValueError("no finite positive timestep bound constructed")
    return {
        "radius":r, "upper_concentration":Q,
        "poisson_potential_bound":float(phi_bound),
        "poisson_lipschitz_bound":float(phi_lipschitz),
        "max_dimensionless_potential_jump":float(u_bound),
        "rhs_sup_bound":M,"rhs_lipschitz_bound":L,
        "sufficient_dt_max":float(dt_upper),
        "theorem":"dt*M<=r/2 and dt*L<=1/2 imply a unique positive exact "
                  "implicit PNP root inside B_inf(c0,r)",
        "uniqueness_scope":"only within the stated positive ball",
        "closed_grounded_constant_permittivity_only":True,
        "computed_float_bounds_not_outward_interval_certified":True,
        "agda_kernel_checked":False,
        "all_timestep_existence_proved":False,
    }


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
    if not np.all(np.isfinite(sol.x)):
        raise RuntimeError('nonfinite implicit log-root candidate')
    sol_residual=np.max(np.abs(residual(sol.x)))
    if not np.isfinite(sol_residual):
        raise RuntimeError('nonfinite implicit residual')
    if not sol.success and sol_residual>rtol:
        raise RuntimeError(f'implicit coupled PNP did not converge: {sol.message}')
    if np.any(np.abs(sol.x)>69): raise RuntimeError('log-iterate clipping invalidated root')
    c=np.exp(sol.x.reshape(c0.shape)); ph=poisson(c,m)
    defect=c-c0-dt*vector_rhs(c,m,ph)
    err=np.max(np.abs(defect))
    if not np.isfinite(err) or err>rtol or not np.all(np.isfinite(c)) or not np.all(np.isfinite(ph)):
        raise RuntimeError(f'coupled residual not paid: {err}')
    e0=free_energy(c0,ph0,m); e1=free_energy(c,ph,m)
    if not np.isfinite(e0) or not np.isfinite(e1):
        raise RuntimeError('nonfinite original PNP free energy')
    if e1>e0+max(1e-9,rtol*max(1,abs(e0))):
        raise RuntimeError(f'free-energy inequality failed: {e0} -> {e1}')
    charge_defect=abs(float(np.dot((c-c0).sum(axis=0),m.z)))
    if not np.isfinite(charge_defect) or charge_defect>max(1e-9,100*rtol):
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