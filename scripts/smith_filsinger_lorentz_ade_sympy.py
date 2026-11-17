"""Exact passive Lorentz-ADE Maxwell Galerkin source model for F13/F15.

A finite closed-curl spatial semidiscretization with n E/H cell degrees
and n Lorentz polarization/momentum degrees; rational coefficients.

 eps E' = C H - sigma E - V + J_nat + J_ctrl
 mu H'  = -C.T E
 P'     = V
 V'     = alpha E - gamma V - omega0**2 P

For eps,mu,alpha,omega0>0 and sigma,gamma>=0:
 U=1/2(eps|E|²+mu|H|²+(|V|²+omega0²|P|²)/alpha).
 Midpoint scheme satisfies exact rational energy law with positive losses.

This does NOT establish hyperbolic 3D Maxwell light cone, actual soil or
ionosphere material data, a continuous retarded dyadic, or measured VI.
"""
from dataclasses import dataclass
import sympy as S

@dataclass(frozen=True)
class LorentzMaterial:
    eps: S.Rational = S.Rational(2)
    mu: S.Rational = S.Rational(3,2)
    sigma: S.Rational = S.Rational(1,5)
    alpha: S.Rational = S.Rational(3,2)
    gamma: S.Rational = S.Rational(2,3)
    omega0sq: S.Rational = S.Rational(4)

    def validated(self):
        p=(self.eps,self.mu,self.alpha,self.omega0sq)
        q=(self.sigma,self.gamma)
        if not all(S.sympify(x).is_positive is True for x in p):
            raise ValueError('positive eps, mu, alpha and resonant stiffness required')
        if not all(S.sympify(x).is_nonnegative is True for x in q):
            raise ValueError('passive nonnegative sigma and gamma required')
        return self


def curl_matrix(n):
    if n<1:raise ValueError('at least one cell')
    return S.Matrix(n,n,lambda i,j:S.Integer(1) if j==i else (
        -S.Integer(1) if j==i+1 else S.Integer(0)))


def generator(n=2, material=None, curl=None, load_conductance=0):
    m=(material or LorentzMaterial()).validated()
    C=curl if curl is not None else curl_matrix(n)
    if C.shape!=(n,n):raise ValueError('curl matrix dimensions')
    load_conductance=S.sympify(load_conductance)
    if load_conductance.is_nonnegative is not True:
        raise ValueError('nonnegative separately metered useful load required')
    ident=S.eye(n);zero=S.zeros(n)
    # state z=(E,H,P,V), four n-vectors; J enters E-equation only.
    A=S.BlockMatrix([
        [-(m.sigma+load_conductance)/m.eps*ident, C/m.eps, zero, -ident/m.eps],
        [-C.T/m.mu, zero, zero, zero],
        [zero, zero, zero, ident],
        [m.alpha*ident, zero, -m.omega0sq*ident, -m.gamma*ident],
    ]).as_explicit()
    B=S.zeros(4*n,n);B[:n,:n]=ident/m.eps
    mass=S.diag(*([m.eps]*n+[m.mu]*n+
                   [m.omega0sq/m.alpha]*n+[1/m.alpha]*n))
    return A,B,mass


def energy(z,mass):
    return S.expand((z.T*mass*z)[0]/2)


def exact_midpoint(z,jn,jc,dt,A,B,mass,load_conductance=0):
    if not S.sympify(dt).is_positive:raise ValueError('dt>0 required')
    n=B.cols
    if any(v.shape!=(n,1) for v in (jn,jc)):
        raise ValueError('source vector dimensions')
    ident=S.eye(A.rows)
    # midpoint unknown (z1+z0)/2; no future source samples are accessed.
    mid=(ident-dt*A/2).inv()*(z+dt*B*(jn+jc)/2)
    z1=2*mid-z
    e=mid[:n,:];v=mid[3*n:4*n,:]
    eps=mass[0,0];alpha=1/mass[3*n,3*n]
    load_conductance=S.sympify(load_conductance)
    if load_conductance.is_nonnegative is not True:
        raise ValueError('nonnegative separate useful load required')
    sigma=S.simplify(-A[0,0]*eps-load_conductance)
    if sigma.is_nonnegative is not True:
        raise ValueError('inconsistent useful-load decomposition')
    gamma=S.simplify(-A[3*n,3*n])
    natural=S.expand(dt*(e.T*jn)[0])
    controller=S.expand(dt*(e.T*jc)[0])
    ohmic=S.expand(dt*sigma*(e.T*e)[0])
    relaxation=S.expand(dt*gamma/alpha*(v.T*v)[0])
    useful_load=S.expand(dt*load_conductance*(e.T*e)[0])
    change=S.expand(energy(z1,mass)-energy(z,mass))
    residual=S.factor(change-natural-controller+ohmic+relaxation+useful_load)
    return dict(initial_state=z,z=z1,mid=mid,energy_change=change,natural_work=natural,
                controller_work=controller,ohmic=ohmic,
                relaxation=relaxation,useful_load=useful_load,residual=residual)


def susceptibility_laplace(s,m=None):
    m=(m or LorentzMaterial()).validated()
    s=S.sympify(s)
    return m.alpha/(s*s+m.gamma*s+m.omega0sq)


def epsilon_effective_laplace(s,m=None):
    m=(m or LorentzMaterial()).validated()
    return m.eps+susceptibility_laplace(s,m)+m.sigma/s


def polarization_convolution_coefficients(m=None):
    """Exact short-time rational Taylor coefficients, not a global PDE Green."""
    m=(m or LorentzMaterial()).validated()
    s=S.symbols('s',positive=True)
    # ODE impulse response g(0)=0, g'(0)=alpha for P''+gamma P'+w²P=alpha E
    # Consecutive derivatives: g''=-gamma*g', g'''=-gamma*g''-w²*g'
    return [S.Integer(0),m.alpha,-m.alpha*m.gamma,
            m.alpha*(m.gamma**2-m.omega0sq)]


def phasor_passivity(omega,m=None):
    """Im chi(omega)>=0 for omega>0, e^{-i omega t} convention."""
    m=(m or LorentzMaterial()).validated();w=S.sympify(omega)
    if w.is_positive is not True:raise ValueError('positive frequency required')
    chi=S.simplify(susceptibility_laplace(-S.I*w,m))
    diss=S.factor(S.im(chi))
    return chi,diss


def lorentz_poles(m=None):
    """Stable causal material poles for positive gamma and underdamping."""
    m=(m or LorentzMaterial()).validated()
    if m.gamma<=0 or 4*m.omega0sq<=m.gamma**2:
        raise ValueError('strictly underdamped dissipative fixture required')
    natural=S.sqrt(m.omega0sq-m.gamma**2/4)
    return (-m.gamma/2+S.I*natural,-m.gamma/2-S.I*natural)


def retarded_impulse(t,m=None):
    """g(t)=alpha/omega_d exp(-gamma*t/2) sin(omega_d*t) for t>=0;
    exactly zero before launch; a temporal *material* memory Green, not a
    3D Maxwell wave light-cone theorem.
    """
    m=(m or LorentzMaterial()).validated()
    if m.gamma<=0 or 4*m.omega0sq<=m.gamma**2:
        raise ValueError('strictly underdamped dissipative fixture required')
    t=S.sympify(t)
    omega=S.sqrt(m.omega0sq-m.gamma**2/4)
    post=S.simplify(m.alpha/omega*S.exp(-m.gamma*t/2)*S.sin(omega*t))
    if t.is_negative is True:return S.Integer(0)
    if t.is_nonnegative is True:return post
    return S.Piecewise((S.Integer(0),t<0),(post,True))


def synthetic_cycle_work_receipt(initial_state, steps, mass):
    """Full state and per-step work auditor for SYNTHETIC data.

    Each step must be from exact_midpoint and in a consecutive timeline.
    An exact algebraic receipt is NOT an independent environmental meter.
    """
    if not steps:raise ValueError('at least one sourced timestep required')
    if any('z' not in entry or 'residual' not in entry
           or 'initial_state' not in entry for entry in steps):
        raise ValueError('missing exact source step receipt')
    if any(S.simplify(entry['residual'])!=0 for entry in steps):
        raise ValueError('broken finite Maxwell/material work identity')
    previous=initial_state
    for entry in steps:
        if entry['initial_state']!=previous:
            raise ValueError('nonconsecutive source/receiver state history')
        previous=entry['z']
    ending=steps[-1]['z']
    natural=S.expand(sum((t['natural_work'] for t in steps),S.Integer(0)))
    controller=S.expand(sum((t['controller_work'] for t in steps),S.Integer(0)))
    load=S.expand(sum((t['useful_load'] for t in steps),S.Integer(0)))
    ohmic=S.expand(sum((t['ohmic'] for t in steps),S.Integer(0)))
    relax=S.expand(sum((t['relaxation'] for t in steps),S.Integer(0)))
    storage=S.expand(energy(ending,mass)-energy(initial_state,mass))
    balance=S.factor(storage+load+ohmic+relax-natural-controller)
    if balance!=0:raise ValueError('incompatible cycle state/work accumulation')
    restored=ending==initial_state
    return dict(restored_all_4n_states=restored,storage_delta=storage,
                natural_work=natural,controller_work=controller,
                useful_load=load,ohmic_loss=ohmic,relaxation_loss=relax,
                conservation_residual=balance,
                original_source_meter_present=False,
                physically_replenished_source_certified=False)
