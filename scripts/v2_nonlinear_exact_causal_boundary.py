#!/usr/bin/env python3
"""Source-independent nonlinear finite-flight multi-winding periodic certificate.

Mathematics: polynomial convex magnetic *energy* U(lambda,z;A), exact
average-vector-field discrete gradients, passive wave scattering, rational
manufactured nonzero periodic state, exact signed rotor-parameter work and
local attraction from the exact Jacobian of the actual implicit nonlinear
period map.  This is NOT a continuum Maxwell field, a physical V2 netlist,
or a global nonlinear attraction/continuous semiconductor certificate.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import inf
import numpy as np
import sympy as sp
from scipy.optimize import root

C=299792458

def rat(x): return x if isinstance(x,Q) else Q(x)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def matvec(a,x): return [dot(row,x) for row in a]
def as_str(x): return str(x)
def pack(f,b,lam,z):return tuple(f)+tuple(b)+tuple(lam)+tuple(z)

@dataclass(frozen=True)
class P:
    m:int=2
    n:int=1
    dt:Q=Q(1,4)
    Z:Q=Q(2)
    s:Q=Q(1,2)
    R:Q=Q(1)
    quartic:Q=Q(1,16)
    g:Q=Q(1,4)
    h:Q=Q(1)
    mu:Q=Q(1)
    speed:Q=Q(2,3)*C
    def check(self,A=None):
        if self.m<2 or self.n<1 or min(self.dt,self.Z,self.R,self.h,self.mu)<=0 or not Q(0)<self.speed<=C or not Q(0)<self.s<=Q(1) or self.quartic<=0:
            raise ValueError('invalid passive physical or finite propagation domain')
        if A is not None:
            if len(A)!=self.m or any(len(row)!=self.m for row in A):raise ValueError('inductance matrix shape')
            if any(A[i][j]!=A[j][i] for i in range(self.m) for j in range(self.m)):raise ValueError('magnetic coupling not reciprocal')
            ell=min((A[i][i]-sum((abs(A[i][j]) for j in range(self.m) if j!=i),Q(0)) for i in range(self.m)))
            if not ell>self.g*self.g/self.h:raise ValueError('joint magnetic energy not uniformly convex')
        return self
    @property
    def length(self):return self.speed*self.dt*self.n
    @property
    def state_dim(self):return 2*self.m*self.n+2*self.m

def A_matrix(p,k):
    # Clocked symmetric spatial coupling, strictly diagonally dominant.
    base=(Q(1),Q(6,5),Q(11,10),Q(4,5))
    a=[[Q(0) for _ in range(p.m)] for _ in range(p.m)]
    for i in range(p.m):
        a[i][i]=base[(k+i)%4]+Q(i,20)
    for i in range(p.m):
        for j in range(i+1,p.m):
            a[i][j]=a[j][i]=Q(1,16*p.m)
    p.check(a)
    return tuple(tuple(row) for row in a)

def magnetic_energy(p,A,lam,z):
    return dot(lam,matvec(A,lam))/2+p.quartic*sum((v**4 for v in lam),Q(0))/4 -p.g*dot(lam,z)+p.h*dot(z,z)/2

def line_energy(p,x):
    return p.dt/p.Z*sum((a*a for a in x[:2*p.m*p.n]),Q(0))

def field_and_line_energy(p,A,x):
    j=2*p.m*p.n
    return line_energy(p,x)+magnetic_energy(p,A,x[j:j+p.m],x[j+p.m:j+2*p.m])

def avf_grad(p,A,lam0,z0,lam1,z1):
    # Exact integral_0^1 grad U((1-t)y0+t y1) dt, not sampled midpoint.
    m=p.m
    mid_l=[(a+b)/2 for a,b in zip(lam0,lam1)]
    mid_z=[(a+b)/2 for a,b in zip(z0,z1)]
    cubic=[(a*a*a+a*a*b+a*b*b+b*b*b)/4 for a,b in zip(lam0,lam1)]
    cur=[t+p.quartic*c-p.g*v for t,c,v in zip(matvec(A,mid_l),cubic,mid_z)]
    force=[p.h*v-p.g*t for t,v in zip(mid_l,mid_z)]
    return tuple(cur),tuple(force)

def secant(p,A,lam0,z0,lam1,z1):
    cur,force=avf_grad(p,A,lam0,z0,lam1,z1)
    delta=dot(cur,(b-a for a,b in zip(lam0,lam1)))+dot(force,(b-a for a,b in zip(z0,z1)))
    return delta == magnetic_energy(p,A,lam1,z1)-magnetic_energy(p,A,lam0,z0)

def step_from_end(p,A,x,u,lam1,z1):
    """Exact rational step, requires supplied endpoint to solve implicit law."""
    p.check(A)
    m,n=p.m,p.n
    if len(x)!=p.state_dim or len(u)!=m:raise ValueError('state/source shape')
    f=list(x[:m*n]);b=list(x[m*n:2*m*n]);lam=x[2*m*n:2*m*n+m];z=x[2*m*n+m:]
    a=tuple(p.s*f[j*n+n-1] for j in range(m))
    returned=tuple(p.s*b[j*n] for j in range(m))
    cur,force=avf_grad(p,A,lam,z,lam1,z1)
    if any(lam1[j]-lam[j]!=p.dt*(2*a[j]-(p.Z+p.R)*cur[j]) for j in range(m)):
        raise ValueError('not an actual nonlinear coupled electrical trajectory')
    if any(z1[j]-z[j]!=-p.dt*p.mu*force[j] for j in range(m)):
        raise ValueError('not an actual magnetic memory trajectory')
    reflected=tuple(a[j]-p.Z*cur[j] for j in range(m))
    voltage=tuple(a[j]+reflected[j] for j in range(m))
    nf=[];nb=[]
    for j in range(m):
        nf.extend((u[j],)+tuple(p.s*f[j*n+t] for t in range(n-1)))
        nb.extend(tuple(p.s*b[j*n+t+1] for t in range(n-1))+(reflected[j],))
    y=pack(nf,nb,lam1,z1)
    src=p.dt/p.Z*(dot(u,u)-dot(returned,returned))
    port=p.dt*dot(voltage,cur)
    loss=p.dt/p.Z*(1-p.s*p.s)*(dot(f,f)+dot(b,b))
    cu=p.dt*p.R*dot(cur,cur)
    mem=p.dt*p.mu*dot(force,force)
    residual=field_and_line_energy(p,A,y)-field_and_line_energy(p,A,x)-(src-loss-cu-mem)
    if residual!=0 or (port-p.dt/p.Z*(dot(a,a)-dot(reflected,reflected)))!=0:
        raise AssertionError('not an exact all-port energy balance')
    return y,dict(source=src,port=port,line_loss=loss,copper=cu,memory=mem,residual=residual,
                  incident=a,reflected=reflected,current=cur)

def numeric_step(p,A,x,u):
    """Independently solve one implicit polynomial boundary step in float.

    The analytic strong-monotonicity theorem justifies unique solvability.
    This numerical implementation is an unvalidated root solve, tested
    against exact manufactured trajectories, *not* an interval enclosure.
    """
    p.check(A);m,n=p.m,p.n;j=2*m*n
    if len(x)!=p.state_dim or len(u)!=m:raise ValueError('state/source shape')
    a=np.array([float(p.s*x[k*n+n-1]) for k in range(m)])
    lam=np.array(x[j:j+m],float);z=np.array(x[j+m:],float)
    AA=np.array(A,float);dt=float(p.dt);D=float(p.Z+p.R)
    g=float(p.g);h=float(p.h);bb=float(p.quartic);mu=float(p.mu)
    def f(v):
        lam1=v[:m];z1=v[m:]
        cur=AA@(lam+lam1)/2 + bb*(lam**3+lam**2*lam1+lam*lam1**2+lam1**3)/4-g*(z+z1)/2
        q=h*(z+z1)/2-g*(lam+lam1)/2
        return np.r_[lam1-lam-dt*(2*a-D*cur),z1-z+dt*mu*q]
    solution=root(f,np.r_[lam,z],tol=1e-12)
    if np.max(np.abs(f(solution.x)))>1e-10:raise RuntimeError('implicit nonlinear step failed')
    lam1=solution.x[:m];z1=solution.x[m:]
    cur=AA@(lam+lam1)/2 + bb*(lam**3+lam**2*lam1+lam*lam1**2+lam1**3)/4-g*(z+z1)/2
    reflected=a-float(p.Z)*cur
    nf=[];nb=[]
    for k in range(m):
        nf.extend((float(u[k]),)+tuple(float(p.s*x[k*n+t]) for t in range(n-1)))
        nb.extend(tuple(float(p.s*x[m*n+k*n+t+1]) for t in range(n-1))+(reflected[k],))
    return np.r_[nf,nb,lam1,z1],float(np.max(np.abs(f(solution.x))))


def periodic_lambdas(p):
    return tuple(tuple(Q(1,2)+Q((3*k+2*j)%5,10) for j in range(p.m)) for k in range(4))

def periodic_memory(p,lams):
    # Solve z1 = alpha*z0 + coeff*(lambda0+lambda1) on a periodic orbit.
    alpha=(1-p.dt*p.mu*p.h/2)/(1+p.dt*p.mu*p.h/2)
    coeff=(p.dt*p.mu*p.g/2)/(1+p.dt*p.mu*p.h/2)
    m=p.m;T=len(lams)
    z0=[]
    for j in range(m):
        b=Q(0)
        for k in range(T):b=alpha*b+coeff*(lams[k][j]+lams[(k+1)%T][j])
        z0.append(b/(1-alpha**T))
    result=[tuple(z0)]
    for k in range(T):
        result.append(tuple(alpha*result[-1][j]+coeff*(lams[k][j]+lams[(k+1)%T][j]) for j in range(m)))
    assert result[0]==result[-1]
    return tuple(result[:-1])

def periodic_manufacture(p,clock_shift=0):
    """Exact *nonzero* orbit and source launches selected at source in advance."""
    p.check()
    T=4;lams=periodic_lambdas(p);zs=periodic_memory(p,lams)
    A=tuple(A_matrix(p,(k+clock_shift)%T) for k in range(T))
    cur=[];inc=[];refl=[]
    for k in range(T):
        i,_=avf_grad(p,A[k],lams[k],zs[k],lams[(k+1)%T],zs[(k+1)%T])
        a=tuple((lams[(k+1)%T][j]-lams[k][j])/p.dt/2+(p.Z+p.R)*i[j]/2 for j in range(p.m))
        cur.append(i);inc.append(a)
        refl.append(tuple(a[j]-p.Z*i[j] for j in range(p.m)))
    # incident[k]=s^n*launch[k-n]; source cannot read future remote state.
    launches=tuple(tuple(inc[(k+p.n)%T][j]/p.s**p.n for j in range(p.m)) for k in range(T))
    def initial_state(k):
        f=[];b=[]
        for j in range(p.m):
            f.extend(p.s**t*launches[(k-1-t)%T][j] for t in range(p.n))
            b.extend(p.s**(p.n-1-t)*refl[(k-(p.n-t))%T][j] for t in range(p.n))
        return pack(f,b,lams[k],zs[k])
    states=[initial_state(k) for k in range(T)]
    totals={key:Q(0) for key in ('source','line_loss','copper','memory','port','rotor_param')}
    for k in range(T):
        nxt,row=step_from_end(p,A[k],states[k],launches[k],lams[(k+1)%T],zs[(k+1)%T])
        if nxt!=states[(k+1)%T]:raise AssertionError('periodicity invalid')
        for key in ('source','line_loss','copper','memory','port'):totals[key]+=row[key]
        # This external signed work includes actual local parameter change.
        q=states[(k+1)%T]
        totals['rotor_param']+=field_and_line_energy(p,A[(k+1)%T],q)-field_and_line_energy(p,A[k],q)
    if totals['source']+totals['rotor_param']!=totals['line_loss']+totals['copper']+totals['memory']:
        raise AssertionError('full-cycle energy inventory not closed')
    return dict(params=p,period=T,A=A,launches=launches,states=states,flux=lams,memory=zs,
                current=tuple(cur),work=totals,model_scope='nonlinear quartic multiwinding exact rational finite-packet energy and periodic orbit')

def step_jacobian(p,A,x,x1):
    """Exact Jacobian of the implicit nonlinear state step, source launch fixed.

    Independent of any finite-difference approximation. The derivative is
    solved by the implicit function theorem at a *known exact orbit point*.
    """
    m,n=p.m,p.n;d=p.state_dim;j=2*m*n
    lam=x[j:j+m];z=x[j+m:];lam1=x1[j:j+m];z1=x1[j+m:]
    dt=sp.Rational(p.dt.numerator,p.dt.denominator)
    def S(q):return sp.Rational(q.numerator,q.denominator)
    aa=sp.Matrix([[S(q) for q in row] for row in A]); eye=sp.eye(m)
    coeff0=[S(p.quartic)*(3*S(a)**2+2*S(a)*S(b)+S(b)**2)/4 for a,b in zip(lam,lam1)]
    coeff1=[S(p.quartic)*(S(a)**2+2*S(a)*S(b)+3*S(b)**2)/4 for a,b in zip(lam,lam1)]
    B0=aa/2+sp.diag(*coeff0)
    B1=aa/2+sp.diag(*coeff1)
    gc=S(p.g);hh=S(p.h);rr=S(p.Z+p.R);mu=S(p.mu);ss=S(p.s);zz=S(p.Z)
    Y=(sp.eye(2*m)+sp.BlockMatrix([[dt*rr*B1,-dt*rr*gc/2*eye],[-dt*mu*gc/2*eye,dt*mu*hh/2*eye]]).as_explicit())
    X=sp.zeros(2*m,d)
    for a in range(m):X[a,a*n+n-1]=-2*dt*ss
    X[:m,j:j+m]=-eye+dt*rr*B0
    X[:m,j+m:j+2*m]=-dt*rr*gc/2*eye
    X[m:2*m,j:j+m]=-dt*mu*gc/2*eye
    X[m:2*m,j+m:j+2*m]=-eye+dt*mu*hh/2*eye
    Dy=-Y.inv()*X
    Xi=sp.zeros(m,d)
    Xi[:,j:j+m]=B0
    Xi[:,j+m:j+2*m]=-gc/2*eye
    Di=Xi+B1*Dy[:m,:]-gc/2*Dy[m:,:]
    J=sp.zeros(d,d)
    for a in range(m):
        for t in range(1,n):
            J[a*n+t,a*n+t-1]=ss
            J[m*n+a*n+t-1,m*n+a*n+t]=ss
        J[m*n+a*n+n-1,a*n+n-1]=ss
    # backward last equals incident minus impedance * current
    for a in range(m):
        J[m*n+a*n+n-1,:]-=zz*Di[a,:]
    J[j:j+2*m,:]=Dy
    return J

def local_attractor(p,cert,power=16):
    states=cert['states'];T=cert['period'];P=sp.eye(p.state_dim)
    for k in range(T):
        J=step_jacobian(p,cert['A'][k],states[k],states[(k+1)%T])
        P=J*P
    # Check rational entries only; ||P^power|| < 1 => LOCAL attraction.
    PP=P**power
    bound=max((sum(abs(PP[i,j]) for j in range(PP.cols)) for i in range(PP.rows)))
    if bound>=1:raise ValueError('not locally contractive for selected iterate')
    return dict(period_derivative_inf_norm=str(max(sum(abs(P[i,j]) for j in range(P.cols)) for i in range(P.rows))),
                contraction_power=power,iterate_inf_norm=str(bound),locally_attracting=True,
                interpretation='local attraction by continuous derivative and exact rational strict norm; NOT global')

def nonlinear_identity_symbolic(m=2):
    # Coefficient identity of U diff against AVF gradient for arbitrary states.
    b,g,h=sp.symbols('b g h',real=True)
    a=sp.symbols('a:'+str(m));w=sp.symbols('w:'+str(m));z=sp.symbols('z:'+str(m));y=sp.symbols('y:'+str(m))
    A=sp.Matrix(m,m,lambda i,j:sp.Symbol('c'+str(min(i,j))+str(max(i,j))))
    l0=sp.Matrix(a);l1=sp.Matrix(w);z0=sp.Matrix(z);z1=sp.Matrix(y)
    U=lambda l,t:(l.T*A*l)[0]/2+b*sum(q**4 for q in l)/4-g*(l.T*t)[0]+h*(t.T*t)[0]/2
    cur=A*(l0+l1)/2+sp.Matrix([b*(l0[j]**3+l0[j]**2*l1[j]+l0[j]*l1[j]**2+l1[j]**3)/4 for j in range(m)])-g*(z0+z1)/2
    q=h*(z0+z1)/2-g*(l0+l1)/2
    residual=sp.expand(U(l1,z1)-U(l0,z0)-(cur.T*(l1-l0))[0]-(q.T*(z1-z0))[0])
    assert residual==0
    return {'phase_count':m,'polynomial_identity_residual':'0','scope':'arbitrary symmetric coupled A and all states, independent of implicit solver'}

def numeric_replay(p,cert):
    # Independently solve nonlinear implicit equations at manufactured orbit.
    err=[]
    for k,x in enumerate(cert['states']):
        A=cert['A'][k];u=cert['launches'][k];n=p.n;m=p.m;j=2*m*n
        a=np.array([float(p.s*x[t*n+n-1]) for t in range(m)])
        lam0=np.array(x[j:j+m],float);z0=np.array(x[j+m:],float)
        AA=np.array(A,float)
        dt=float(p.dt);R=float(p.R+p.Z);g=float(p.g);h=float(p.h);mu=float(p.mu);bb=float(p.quartic)
        def residual(v):
            lam1=v[:m];z1=v[m:];cur=AA@(lam1+lam0)/2 + bb*(lam0**3+lam0**2*lam1+lam0*lam1**2+lam1**3)/4 -g*(z0+z1)/2
            q=h*(z0+z1)/2-g*(lam0+lam1)/2
            return np.r_[lam1-lam0-dt*(2*a-R*cur),z1-z0+dt*mu*q]
        target=np.array(cert['states'][(k+1)%cert['period']][j:],float)
        sol=root(residual,np.r_[lam0,z0],tol=1e-12)
        err.append(max(np.max(np.abs(residual(sol.x))),np.max(np.abs(sol.x-target))))
    return max(err)

def clocked_rotor_work_error_bound(flux_sup,flux_slew_sup,clock_step_s,operator_total_variation):
    """Conditional smooth-rotor work approximation error.

    If ||lambda||<=B and ||dot(lambda)||<=D (Euclidean norms), A(t) is
    absolutely continuous and symmetric, and TV(A)=integral ||dot A||dt,
    then replacing continuous parameter work by right-endpoint clock jumps
    gives absolute error <=B*D*h*TV(A). The bounds are ASSUMED input,
    not established for the original nonlinear Maxwell-machine system.
    This theorem does not apply to unbounded slew or unmodelled switch edges.
    """
    inputs=(flux_sup,flux_slew_sup,clock_step_s,operator_total_variation)
    if any(not np.isfinite(x) or x<0 for x in inputs) or clock_step_s<=0:
        raise ValueError('positive finite Lipschitz domain is required')
    return float(flux_sup*flux_slew_sup*clock_step_s*operator_total_variation)


def run():
    # Nonzero *generator-polarity* example: rotor work enters and electrical
    # work exits at the source, while copper/memory/line dissipation is paid.
    # Abstract dt=0.25s means VERY LONG cable: not an original V2 geometry.
    p=P(m=3,n=1,s=Q(999,1000),R=Q(1,100),Z=Q(1,2))
    c=periodic_manufacture(p,clock_shift=2)
    attr=local_attractor(p,c,power=1)
    assert c["work"]["rotor_param"]>0 and c["work"]["source"]<0
    assert c["work"]["line_loss"]>0
    return {'model':'nonlinear quartic coupled magnetic-memory generator with strictly causal finite packet transport',
            'symbolic_identity':nonlinear_identity_symbolic(3),'periodic_work':{k:str(v) for k,v in c['work'].items()},
            'periodic_endpoint_exact':True,'causal_flight_ticks':p.n,'implied_cable_length_m':float(p.length),
            'periodic_nonzero_state':True,'local_attractor':attr,
            'nonlinear_implicit_step_numeric_error':numeric_replay(p,c),
            'physical_speed_m_per_s':float(p.speed),'original_device':'NOT reconstructed',
            'open':['realistic meter-scale cable and mechanical-cycle validated multirate coupling','global attraction for unrestricted nonlinear motor','arbitrary Preisach hysteresis','physical rotor and semiconductor edge dynamics','spatial Maxwell to conductor fields','original V2 calibrated full energy boundary','Agda kernel proof']}
if __name__=='__main__': print(json.dumps(run(),indent=2))
