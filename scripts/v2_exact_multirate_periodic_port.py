#!/usr/bin/env python3
"""Exact, finite-speed, passive line + linear lag-memory motor certificate.

A *restricted* rational hybrid system: n positive-flight packet cells;
midpoint (discrete-gradient) motor boundary; linear reversible magnetic
coupling g and dissipative relaxation z; a LOCAL piecewise constant inductance
L_k representing a clocked rotor parameter. Its changes have EXTERNAL signed
mechanical/modulation work. Drive waves are supplied at the source only.

Block matrix powers are exact for a constant L and held launch input; they
retain all terminal, source, copper, memory and line-loss work via quadratic
Gramians. Periodic state uniqueness is certified by a strict rational
infinity-norm contraction of a power of the period map. This is not a
continuum Maxwell/PDE result, a smooth rotating machine, an actual V2 netlist,
or real-rate hysteresis. Geometry v <= c must be supplied separately.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction as F
from functools import reduce
import json
import math
import numpy as np

C0=299792458

def f(x):
    return x if isinstance(x,F) else F(x)

def mat_zero(n,m):return [[F(0) for _ in range(m)] for _ in range(n)]
def mat_eye(n):
    a=mat_zero(n,n)
    for i in range(n):a[i][i]=F(1)
    return a

def mv(A,x):return [sum((t*z for t,z in zip(row,x)),F(0)) for row in A]
def mm(A,B):
    Bt=list(zip(*B));return [[sum((a*b for a,b in zip(row,col)),F(0)) for col in Bt] for row in A]
def mt(A):return list(map(list,zip(*A)))
def madd(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def neg(A):return [[-a for a in row] for row in A]
def msub(A,B):return madd(A,neg(B))
def quadratic(Q,x):return sum((a*b for a,b in zip(x,mv(Q,x))),F(0))
def norm_inf(A):return max(sum((abs(x) for x in row),F(0)) for row in A)

def solve(A,b):
    a=[row[:]+[v] for row,v in zip(A,b)]
    n=len(b)
    for k in range(n):
        pivot=next((j for j in range(k,n) if a[j][k]),None)
        if pivot is None:raise ValueError('singular period map')
        a[k],a[pivot]=a[pivot],a[k]
        d=a[k][k]
        for j in range(k,n+1):a[k][j]/=d
        for i in range(n):
            if i==k:continue
            r=a[i][k]
            for j in range(k,n+1):a[i][j]-=r*a[k][j]
    return [a[i][n] for i in range(n)]

@dataclass(frozen=True)
class Params:
    n:int=2
    dt:F=F(1,4)
    Z:F=F(2)
    s:F=F(1,2)
    R:F=F(1)
    g:F=F(1,4)
    h:F=F(1)
    mu:F=F(1)
    front_m_s:F=F(2,3)*C0
    def check(self):
        if self.n<1 or self.dt<=0 or self.Z<=0 or self.R<=0 or self.h<=0 or self.mu<0:raise ValueError('invalid positive physical parameter')
        if not 0<=self.s<=1:raise ValueError('active gain in passive line')
        if not 0<self.front_m_s<=C0:raise ValueError('superluminal or negative wave front')
        return self
    @property
    def cable_length_m(self):return self.n*self.dt*self.front_m_s
    @property
    def one_way_s(self):return self.n*self.dt


def field_energy(p:Params,L,x):
    lam,z=x[-2:]
    return (lam-p.g*z)**2/(2*L)+p.h*z*z/2

def total_energy(p:Params,L,x):
    return p.dt/p.Z*sum((a*a for a in x[:-2]),F(0))+field_energy(p,L,x)


def step(p:Params,L,x,u):
    """Exact rational linear discrete gradient and wave scattering step."""
    p.check();L=f(L);u=f(u)
    if L<=0:raise ValueError('positive differential inductance required')
    if len(x)!=2*p.n+2:raise ValueError('state shape mismatch')
    n=p.n
    forward=x[:n];backward=x[n:2*n]
    lam,z=x[-2:]
    incident=p.s*forward[-1]
    returning=p.s*backward[0]
    alpha=p.dt*(p.Z+p.R)/(2*L)
    beta=p.dt*(p.Z+p.R)*p.g/(2*L)
    delta=p.dt*p.mu*p.g/(2*L)
    eps=p.dt*p.mu*(p.g*p.g/L+p.h)/2
    rhs1=(1-alpha)*lam+beta*z+2*p.dt*incident
    rhs2=delta*lam+(1-eps)*z
    det=(1+alpha)*(1+eps)-beta*delta
    if det<=0:raise ValueError('nonpassive implicit update')
    lam1=((1+eps)*rhs1+beta*rhs2)/det
    z1=(delta*rhs1+(1+alpha)*rhs2)/det
    mid_i=((lam+lam1)-p.g*(z+z1))/(2*L)
    mid_z=(z+z1)/2
    drive=p.g*mid_i-p.h*mid_z
    reflected=incident-p.Z*mid_i
    v=incident+reflected
    new_f=[u]+[p.s*w for w in forward[:-1]]
    new_b=[p.s*w for w in backward[1:]]+[reflected]
    x1=new_f+new_b+[lam1,z1]
    out={
        'source':p.dt/p.Z*(u*u-returning*returning),
        'motor_port':p.dt*v*mid_i,
        'line_loss':p.dt/p.Z*(1-p.s*p.s)*sum((w*w for w in forward+backward),F(0)),
        'copper':p.dt*p.R*mid_i*mid_i,
        'memory':p.dt*p.mu*drive*drive,
    }
    out['balance']=total_energy(p,L,x1)-total_energy(p,L,x)-(out['source']-out['copper']-out['memory']-out['line_loss'])
    out['line_motor_port_balance']=out['motor_port']-p.dt/p.Z*(incident*incident-reflected*reflected)
    return x1,out


def coefficient_matrix(p,L):
    """Affine micro-step: x_next=A*x+B*u, all Fraction."""
    d=2*p.n+2
    base=[F(0)]*d
    B,_=step(p,L,base,F(1))
    cols=[]
    for j in range(d):
        x=base[:];x[j]=F(1)
        col,_=step(p,L,x,F(0));cols.append(col)
    return mt(cols),B


def symmetric_quadratic(function,d):
    out=mat_zero(d,d)
    zero=[F(0)]*d
    diag=[]
    for i in range(d):
        e=zero[:];e[i]=F(1)
        diag.append(function(e));out[i][i]=diag[-1]
    for i in range(d):
        for j in range(i+1,d):
            x=zero[:];x[i]=x[j]=F(1)
            c=(function(x)-diag[i]-diag[j])/2
            out[i][j]=out[j][i]=c
    return out


def one_step_certificate(p,L):
    """Coefficient-wise rational identity for *every* state and launch."""
    d=2*p.n+2
    A,B=coefficient_matrix(p,L)
    M=mat_zero(d+1,d+1)
    for i in range(d):
        M[i][:d]=A[i]
        M[i][d]=B[i]
    M[d][d]=F(1)
    H=symmetric_quadratic(lambda x:total_energy(p,L,x[:d]),d+1)
    names=['source','motor_port','line_loss','copper','memory']
    Q={name:symmetric_quadratic(lambda x,field=name:step(p,L,x[:d],x[d])[1][field],d+1) for name in names}
    diff=msub(mm(mm(mt(M),H),M),H)
    rhs=msub(msub(msub(Q['source'],Q['line_loss']),Q['copper']),Q['memory'])
    if diff!=rhs:raise AssertionError('matrix energy identity false')
    return M,Q,H


def compose(left,right):
    """Transition left THEN right, with all quadratic receipts accumulated."""
    ML,QL=left;MR,QR=right
    MP=mm(MR,ML)
    QP={key:madd(QL[key],mm(mm(mt(ML),QR[key]),ML)) for key in QL}
    return MP,QP


def superstep(p,L,k):
    """Binary powering O(log k) block assemblies; held L and held u."""
    if not isinstance(k,int) or k<0:raise ValueError('nonnegative integer block length required')
    M,Q,_=one_step_certificate(p,L)
    acc=(mat_eye(len(M)),{key:mat_zero(len(M),len(M)) for key in Q})
    base=(M,Q)
    while k:
        if k&1:acc=compose(acc,base)
        k//=2
        if k:base=compose(base,base)
    return acc


def augment(x,u):return x+[f(u)]

def fraction_receipts(p,L,x,u,k):
    M,Q=superstep(p,L,k)
    y=augment(x,u)
    end=mv(M,y)[:-1]
    receipts={name:quadratic(A,y) for name,A in Q.items()}
    receipts['energy_change']=total_energy(p,L,end)-total_energy(p,L,x)
    receipts['energy_residual']=receipts['energy_change']-(receipts['source']-receipts['line_loss']-receipts['copper']-receipts['memory'])
    return end,receipts


def explicit_steps(p,L,x,u,k):
    out={name:F(0) for name in ['source','motor_port','line_loss','copper','memory']}
    for _ in range(k):
        x,row=step(p,L,x,u)
        for key in out:out[key]+=row[key]
        assert row['balance']==0 and row['line_motor_port_balance']==0
    return x,out



def floating_superstep(p:Params,L,k:int,relative_rounding_expected=True):
    """Fast *numerical* O(log k) execution of the exact-model block algebra.

    The one-step coefficient identities are derived with Fractions. Converting
    them to float is NOT an interval proof at k~millions; a post-run energy
    residual and two-block semigroup control are mandatory. No CPU stepping
    through every fine-grained light-flight tick is used.
    """
    if not isinstance(k,int) or k<0:raise ValueError('nonnegative block length')
    M,Q,_=one_step_certificate(p,L)
    base=(np.array(M,float),{a:np.array(b,float) for a,b in Q.items()})
    d=len(M)
    acc=(np.eye(d),{name:np.zeros((d,d)) for name in Q})
    def combine(x,y):
        X,QX=x;Y,QY=y
        return Y@X,{key:QX[key]+X.T@QY[key]@X for key in QX}
    while k:
        if k&1:acc=combine(acc,base)
        k//=2
        if k:base=combine(base,base)
    return acc


def float_receipts(p,L,x,u,k):
    M,Q=floating_superstep(p,L,k)
    y=np.array([float(t) for t in x]+[float(u)])
    end=(M@y)[:-1]
    work={key:float(y@v@y) for key,v in Q.items()}
    energy_change=float(total_energy_float(p,L,end)-total_energy_float(p,L,np.array(x,float)))
    work['energy_change']=energy_change
    work['energy_residual']=energy_change-(work['source']-work['line_loss']-work['copper']-work['memory'])
    return end,work


def total_energy_float(p,L,x):
    lam,z=x[-2:]
    return float(p.dt/p.Z)*np.dot(x[:-2],x[:-2])+(lam-float(p.g)*z)**2/(2*float(L))+float(p.h)*z*z/2


def long_cable_microtick_example():
    """Illustrative 0.5m line at .7c, ONE propagation cell and held rotor.

    The 10.7M tiny steps are grouped algebraically under constant parameters.
    There is NO claim the rotor is frozen for a real cycle, nor that continuous
    switching edges are resolved when the launch is held at a constant 0.2 V.
    """
    cable_m=.5
    dt=F(5,10)/F('209854720.6')
    p=Params(n=1,dt=dt,Z=F(6),s=F('0.995'),R=F(1),g=F('.002'),h=F('.004'),mu=F(5500),
             front_m_s=F('209854720.6'))
    k=round(float((F(60)/2354)/dt))
    x=[F(0)]*(2*p.n+2)
    end,work=float_receipts(p,F('.04'),x,F('.2'),k)
    if abs(work['energy_residual'])>2e-9:raise AssertionError('float macro balance too large')
    return {'flight_s':float(dt),'cable_m':float(p.cable_length_m),
            'microticks_for_2354rpm_period':k,'source_wave_v':.2,
            'held_local_inductance_h':.04,'state_final':[float(z) for z in end],
            'work_j':work,'numerical_method':'binary affine/Gramian powering; source and reluctance held fixed',
            'limitation':'no mechanical rotation resolved, no retarded continuum Maxwell, no interval rounding proof'}

def periodic_certificate(p=Params(), Ls=(F(1),F(5,4),F(1),F(3,4)),
                         us=(F(1),F(0),F(-1),F(0)), block_length=2,
                         contraction_power=16):
    """Exact periodic, piecewise-local reluctance model; no smooth rotor claim."""
    if len(Ls)!=len(us) or not len(Ls):raise ValueError('period mismatch')
    if any(L<=0 for L in Ls):raise ValueError('passive inductance domain')
    d=2*p.n+2
    P=mat_eye(d+1)
    for L,u in zip(Ls,us):
        M,_=superstep(p,L,block_length)
        # replace last column so physical affine constant 1 -> launch u
        M2=[row[:] for row in M]
        for i in range(d):M2[i][d]*=u
        P=mm(M2,P)
    A=[row[:d] for row in P[:d]];B=[row[d] for row in P[:d]]
    power=mat_eye(d)
    for _ in range(contraction_power):power=mm(A,power)
    contraction=norm_inf(power)
    if contraction>=1:
        raise ValueError('no certified strict contraction at selected iterate')
    fixed=solve(msub(mat_eye(d),A),B)
    if mv(P,fixed+[F(1)])[:-1]!=fixed:
        raise AssertionError('fixed point not exact')
    x=fixed[:]
    totals={key:F(0) for key in ['source','motor_port','line_loss','copper','memory','local_mechanical']}
    for j,(L,u) in enumerate(zip(Ls,us)):
        x,rec=fraction_receipts(p,L,x,u,block_length)
        for key in ['source','motor_port','line_loss','copper','memory']:totals[key]+=rec[key]
        if rec['energy_residual']!=0:raise AssertionError('block balance failed')
        Lnext=Ls[(j+1)%len(Ls)]
        totals['local_mechanical']+=field_energy(p,Lnext,x)-field_energy(p,L,x)
    if x!=fixed:raise AssertionError('periodic state not exact')
    total_error=totals['source']+totals['local_mechanical']-totals['line_loss']-totals['copper']-totals['memory']
    if total_error!=0:raise AssertionError('periodic signed energy law false')
    return {'d':d,'period_ticks':len(Ls)*block_length,'contraction_iterate':contraction_power,
            'contraction_inf_norm':str(contraction),'fixed_state_fraction':[str(a) for a in fixed],
            'source_work':str(totals['source']),'local_mechanical_work':str(totals['local_mechanical']),
            'copper_loss':str(totals['copper']),'memory_loss':str(totals['memory']),
            'line_loss':str(totals['line_loss']), 'period_energy_residual':'0',
            'source_work_float':float(totals['source']),
            'local_mechanical_work_float':float(totals['local_mechanical']),
            'line_loss_float':float(totals['line_loss']),
            'copper_loss_float':float(totals['copper']),
            'memory_loss_float':float(totals['memory'])}


def physical_delay_bound(cable_m=.5,speed_ratio=.7):
    if not 0<speed_ratio<=1 or cable_m<=0:raise ValueError('positive subluminal cable')
    tau=cable_m/(speed_ratio*C0)
    return {'cable_m':cable_m,'front_speed_m_s':speed_ratio*C0,'earliest_oneway_s':tau,
            'motor_period_2354rpm_s':60/2354,'motor_ticks_per_period_if_micro_dt':(60/2354)/tau,
            'scope':'illustrative cable and motor RPM only; no V2 cable geometry or PWM edge waveform'}


def run():
    p=Params()
    cert=periodic_certificate(p)
    _,r=fraction_receipts(p,F(1),[F(0)]*(2*p.n+2),F(1),12)
    if r['energy_residual']!=0:raise AssertionError('energy')
    return {'model':'restricted rational passive waveguide/magnetic-lag/clocked-reluctance reduction',
            'exact_matrix_all_states':True,'block12_source_energy':str(r['source']),
            'block12_copper':str(r['copper']),'block12_memory':str(r['memory']),
            'block12_line_loss':str(r['line_loss']),
            'block12_energy_residual':str(r['energy_residual']),
            'periodic_certificate':cert,'delay_scale':physical_delay_bound(),
            'held_cable_multirate':long_cable_microtick_example(),
            'not_proved':['continuous spatial Maxwell','smooth rotor with parametric time variation',
                'nonlinear saturation with numerical interval flow','arbitrary hysteresis or actual PWM',
                'Agda kernel or source-identical original V2 measurements']}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
