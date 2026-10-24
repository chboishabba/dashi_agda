"""Exact B fixed-output ORIGINAL covariance → physical rate and six R236 blocks.

Source owners:
NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact.agda
NSTriadKNFixedOutputPhysicalCoherentCovarianceCriticalRegionLiveExact.agda
NSTriadKNR650RateKernelCommutatorEndpointRound685Exact.agda

These tests target universal algebra with a literal same-output physical
triad/rate fibre. The complex A_tau are algebraic input values, not a
separately verified helical velocity realization. They test identity,
NOT a uniform signed estimate or completion of Clay B.
"""
from itertools import combinations
import sympy as S

I=S.I
OUTPUT=(64,1,0)
PAIRS=(
  ((1,0,0),(63,1,0)),
  ((63,1,0),(1,0,0)),
  ((32,0,0),(32,1,0)),
  ((2048,0,0),(-1984,1,0))
)
A=(1+I,2-I,S.Integer(3),-2*I)

def norm2(m):return sum(x*x for x in m)
def shell(m):
    n=max(map(abs,m))
    return 0 if n<=1 else (n-1).bit_length()
def region(p,q):
    assert tuple(x+y for x,y in zip(p,q))==OUTPUT
    jp,jq,jk=map(shell,(p,q,OUTPUT))
    if jp+3<jq: return "DFL" if 3*jp<=2*jq else "Core"
    if jq+3<jp: return "DFL" if 3*jq<=2*jp else "Core"
    if jk+3<jp and jk+3<jq:
        return "DHH" if 5*jk<=4*max(jp,jq) else "Core"
    return "Core"
def work(a,b):return S.expand(S.conjugate(a)*b+a*S.conjugate(b))
def covariance(values,pairs,nu):
    m=sum(values)
    mass=[norm2(p)+norm2(q) for p,q in pairs]
    rates=[nu*z for z in mass]
    decay=-sum(r*a for r,a in zip(rates,values))
    return S.expand(len(values)*work(m,decay)+sum(rates)*work(m,m))
def six_pair_blocks(values,pairs):
    m=sum(values);mass=[norm2(p)+norm2(q) for p,q in pairs]
    result={}
    for i,j in combinations(range(len(pairs)),2):
        tags=tuple(sorted((region(*pairs[i]),region(*pairs[j]))))
        result[tags]=result.get(tags,0)+(
            (mass[i]-mass[j])*(work(m,values[i])-work(m,values[j])))
    return result

def test_physical_rate_and_commutator_tangent_exact():
    nu=S.Integer(2);m=sum(A); n=len(A)
    rates=[nu*(norm2(p)+norm2(q)) for p,q in PAIRS]
    D=-sum(r*a for r,a in zip(rates,A))
    C=covariance(A,PAIRS,nu)
    K=sum(r*work(m,a) for r,a in zip(rates,A))
    R=sum(rates)
    tangent=3+4*I
    commutator=tangent-D
    assert C==780398656
    assert S.expand(C-R*work(m,m)+n*K)==0
    assert S.expand(C-R*work(m,m)+n*(
        work(m,commutator)-work(m,tangent)))==0

def test_six_region_source_defined_rate_difference_identity():
    nu=S.Integer(2)
    blocks=six_pair_blocks(A,PAIRS)
    assert {region(*pair) for pair in PAIRS}=={"DFL","DHH","Core"}
    assert S.expand(covariance(A,PAIRS,nu)+nu*sum(blocks.values()))==0
    assert blocks[("DFL","DHH")]==-162531800
    assert blocks[("DHH","Core")]==-227598336

def test_quartic_scaling_and_zero_padding_negative_control():
    nu=S.Integer(2); old=covariance(A,PAIRS,nu)
    for a in (1,2,3):
        scaled=tuple(a*a*z for z in A)
        assert S.expand(covariance(scaled,PAIRS,nu)-a**4*old)==0
    # A zero-amplitude extra incidence changes n and rate-sum, despite
    # leaving all actual nonzero physical amplitudes and M unchanged.
    padded=PAIRS+(((4096,0,0),(-4032,1,0)),)
    assert covariance(A+(0,),padded,nu)!=old
