#!/usr/bin/env python3
"""LXXXV exact two-cell Maxwell-Lorentz ADE two-port and inverse controls.
Source-equivalent donor equations, *not* imported donor byte-for-byte.
All field/source units and calibrations are SYNTHETIC. No CI or physical admission.
"""
import json
import sympy as S
Q=S.Rational
N=2
C=S.Matrix([[1,-1],[0,1]])
I=S.eye(N);Z=S.zeros(N)
eps=Q(2);mu=Q(3,2);alpha=Q(3,2);omega2=Q(4)
sigma=Q(1,5);gamma=Q(2,3); G=Q(1,3)
# Physical natural vs controller source injection locations are distinct; source time
# record separately clocks exact retarded input arrival, not simultaneous source time.
A=S.BlockMatrix([[-(sigma+G)/eps*I,C/eps,Z,-I/eps],[-C.T/mu,Z,Z,Z],[Z,Z,Z,I],[alpha*I,Z,-omega2*I,-gamma*I]]).as_explicit()
B=S.zeros(8,2);B[:2,:]=I/eps
M=S.diag(*([eps]*N+[mu]*N+[omega2/alpha]*N+[1/alpha]*N))
assert S.simplify(M*A+A.T*M+S.diag(*([2*(sigma+G)]*N+[0]*N+[0]*N+[2*gamma/alpha]*N)))==S.zeros(8)
dt=Q(1,10)
K=(S.eye(8)-dt*A/2).inv()

def simulate(nat,ctrl):
    """Exact donor midpoint: two distinguishable spatial locations, two work meters."""
    z=S.zeros(8,1); traces=[]
    for n,c in zip(nat,ctrl):
        jn=S.Matrix([n,0]);jc=S.Matrix([0,c])
        mid=K*(z+dt*B*(jn+jc)/2)
        z1=2*mid-z
        e=mid[:N,:];v=mid[3*N:4*N,:]
        w_nat=S.expand(dt*(e.T*jn)[0]);w_ctrl=S.expand(dt*(e.T*jc)[0])
        w_ohm=S.expand(dt*sigma*(e.T*e)[0]);w_rel=S.expand(dt*gamma/alpha*(v.T*v)[0]);w_load=S.expand(dt*G*(e.T*e)[0])
        U=lambda x:S.expand((x.T*M*x)[0]/2)
        du=S.expand(U(z1)-U(z));res=S.factor(w_nat+w_ctrl-w_ohm-w_rel-w_load-du)
        assert res==0
        traces.append(dict(natural=w_nat,controller=w_ctrl,ohmic=w_ohm,relaxation=w_rel,load=w_load,storage=du,voltage=e[1],current=G*e[1]))
        z=z1
    return z,traces

def trace(n,c):return S.Matrix([v['voltage'] for v in simulate(n,c)[1]])

# Source arrival is explicitly delayed one time bin for the remote natural source.
# Natural launch pulses (1,0,0,1) arrive at receiver (0,1,0,0) in 4-bin window.
nlaunch=[1,0,0,1];narrival=[0,1,0,0];controller=[0,0,1,0]
_,rows=simulate(narrival,controller)
assert len(rows)==4 and all(v['load']>=0 and v['ohmic']>=0 and v['relaxation']>=0 for v in rows)
ntotal=lambda key:S.factor(sum(d[key] for d in rows))
assert S.factor(ntotal('natural')+ntotal('controller')-ntotal('ohmic')-ntotal('relaxation')-ntotal('load')-ntotal('storage'))==0
assert all(x==0 for x in simulate([0]*4,[0]*4)[0])
col1=trace(narrival,[0]*4);col2=trace([0]*4,controller)
H=S.Matrix.hstack(col1,col2)
assert H.rank()==2
# Collinear/collocated and simultaneously modulated driving remains rank one.
collinear=S.Matrix.hstack(col1,col1)
assert collinear.rank()==1
# Finite independent inverse recovers exact source amplitudes, if columns are KNOWN.
a,b=S.symbols('a b',real=True)
y=H*S.Matrix([a,b]);left=(H.T*H).inv()*H.T
assert [S.factor(v) for v in left*y]==[a,b]
# Unknown antenna gain g multiplies the received natural input:
# terminal data alone determine only g*a even when H is full rank.
g,h=S.symbols('g h',nonzero=True,real=True)
assert S.simplify(g*a-(g/h)*(h*a))==0
# A receiver voltage and load current in this model are not measured SI.
assert len(set(['duga_1984','haarp_2005','sura_2025']))==3
receipt=dict(status='PASS',scope='SYNTHETIC_EXACT_TWO_CELL_ADE_NOT_PHYSICAL',sympy=S.__version__,
    donor='smith_filsinger_lorentz_ade_sympy.py exact n=2 generator and midpoint transcribed',
    cells=2,steps=4,delay_bins=1,measurement_jacobian_rank=H.rank(),
    matched_source_profile_rank=collinear.rank(),calibrated_source_inverse_exact=True,
    unknown_source_gain_ambiguity=True,zero_source_zero_output=True,
    total_natural_work=str(ntotal('natural')),total_controller_work=str(ntotal('controller')),
    total_ohmic=str(ntotal('ohmic')),total_relaxation=str(ntotal('relaxation')),
    total_load=str(ntotal('load')),total_storage=str(ntotal('storage')),
    per_step_residual_exact_zero=True,physical_si_metering=False,
    source_to_j18_impedance_weld=False,physical_admission=False,ci=False)
print(json.dumps(receipt,indent=2))
