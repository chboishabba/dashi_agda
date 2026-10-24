"""Exact physical Fourier Navier–Stokes curl identity and strict R63/R236 partition.

Sources: standard curl/strain identities (Temam); Bony, Bahouri–Chemin–Danchin;
DASHI source owners PhysicalScaleTrichotomy, LuoPhysicalFiveClassSupportRound25,
PhysicalParabolicCriticalRegionRouting. This is NOT the R685 mixed-helicity
functional, nor a proof of B7 or unrestricted Clay B.
"""
from collections import defaultdict
import sympy as S

I=S.I
def vec(k): return S.Matrix(k)
def conjdot(u,v): return (S.conjugate(u).T*v)[0]
def add(p,q): return tuple(p[j]+q[j] for j in range(3))
def neg(p): return tuple(-x for x in p)
def norm2(k): return sum(x*x for x in k)
def shell(k):
    n=max(map(abs,k))
    return 0 if n<=1 else (n-1).bit_length()
def bony(p,q):
    k=add(p,q); jp,jq,jk=shell(p),shell(q),shell(k)
    if jp+3<jq:return "LH"
    if jq+3<jp:return "HL"
    if jk+3<jp and jk+3<jq:return "HH"
    return "CC"
def r236(p,q):
    k=add(p,q); jp,jq,jk=shell(p),shell(q),shell(k)
    tag=bony(p,q)
    if tag=="LH" and 3*jp<=2*jq:return "deep-LH"
    if tag=="HL" and 3*jq<=2*jp:return "deep-HL"
    if tag=="HH" and 5*jk<=4*max(jp,jq):return "deep-HH"
    return "critical"

def budget(u):
    """Exact curl and signed production identities for a real finite
    transverse Fourier field, including *all generated* output modes.
    The R236 result is a decomposition by the SOURCE CLASSIFIER ONLY,
    not by the separately typed critical-production consumer.
    """
    for k,v in u.items():
        assert vec(k).dot(v)==0
        assert neg(k) in u and u[neg(k)]==S.conjugate(v)
    omega={k:I*vec(k).cross(v) for k,v in u.items()}
    bt=defaultdict(lambda:S.Integer(0))
    rt=defaultdict(lambda:S.Integer(0))
    rcorrections=defaultdict(lambda:[S.Integer(0)]*4)
    corrections=defaultdict(lambda:[S.Integer(0)]*4)
    total=energy=transport=stretch=S.Integer(0)
    for k in {add(p,q) for p in u for q in u}:
        conv=S.zeros(3,1); adv=S.zeros(3,1); vortex=S.zeros(3,1)
        for p,up in u.items():
            q=tuple(k[j]-p[j] for j in range(3))
            if q not in u:continue
            dot=vec(q).dot(up)
            conv+=dot*u[q]
            adv+=-I*dot*omega[q]
            vortex+=I*vec(q).dot(omega[p])*u[q]
        N=-I*conv
        projected=N-vec(k)*(vec(k).dot(N))/norm2(k) if norm2(k) else N
        assert all(S.simplify(x)==0 for x in I*vec(k).cross(N)-adv-vortex),k
        assert all(S.simplify(x)==0 for x in I*vec(k).cross(projected)-I*vec(k).cross(N)),k
        if k not in u:continue
        uk=u[k]; wk=omega[k]
        assert S.simplify(conjdot(uk,N)-conjdot(uk,projected))==0
        E=2*S.re(conjdot(uk,projected))
        W=2*S.re(conjdot(wk,I*vec(k).cross(projected)))
        A=2*S.re(conjdot(wk,adv))
        V=2*S.re(conjdot(wk,vortex))
        assert S.simplify(W-norm2(k)*E)==0
        assert S.simplify(W-A-V)==0
        energy+=E; total+=W; transport+=A; stretch+=V
        for p,up in u.items():
            q=tuple(k[j]-p[j] for j in range(3))
            if q not in u:continue
            pair=-I*vec(q).dot(up)*u[q]
            cell=S.simplify(2*S.re(conjdot(uk,pair))*norm2(k))
            bt[bony(p,q)]+=cell
            region=r236(p,q)
            rt[region]+=cell
            advCell=-I*vec(q).dot(up)*omega[q]
            stretchCell=I*vec(q).dot(omega[p])*u[q]
            Tcell=2*S.re(conjdot(wk,advCell))
            Scell=2*S.re(conjdot(wk,stretchCell))
            delta=S.simplify(cell-Tcell-Scell)
            tag=bony(p,q)
            corrections[tag]=[
                corrections[tag][i]+value for i,value
                in enumerate((cell,Tcell,Scell,delta))]
            rcorrections[region]=[
                rcorrections[region][i]+value for i,value
                in enumerate((cell,Tcell,Scell,delta))]
    assert S.simplify(energy)==S.simplify(transport)==0
    assert S.simplify(total-stretch)==0
    assert S.simplify(sum(bt.values())-total)==0
    assert S.simplify(sum(rt.values())-total)==0
    assert S.simplify(sum(v[3] for v in corrections.values()))==0
    # Each R236 region is closed under (p,q) <-> (q,p). The
    # pairwise curl defect therefore cancels INSIDE each region.
    assert all(S.simplify(v[3])==0 for v in rcorrections.values())
    assert S.simplify(sum(v[1] for v in corrections.values()))==0
    return {"production":S.simplify(total),"stretch":S.simplify(stretch),
            "transport":S.simplify(transport),"energy":S.simplify(energy),
            "bony":{k:S.simplify(v) for k,v in bt.items()},
            "r236":{k:S.simplify(v) for k,v in rt.items()},
            "class_correction":{k:tuple(map(S.simplify,v)) for k,v in corrections.items()},
            "region_correction":{k:tuple(map(S.simplify,v)) for k,v in rcorrections.items()}}

def field(p,q):
    """Transverse six-mode rational/integer-coefficient calibration."""
    k=add(p,q)
    def basis(m):
        m=vec(m); e=vec((0,0,1))
        if m.cross(e)==S.zeros(3,1):e=vec((1,0,0))
        return m.cross(e)
    result={p:basis(p),q:basis(q),k:I*basis(k)}
    result.update({neg(m):S.conjugate(v) for m,v in list(result.items())})
    return result

def ordered_curl_residual(p,q,up,uq):
    """Polynomial ordered curl defect, with common Fourier phases factored."""
    return vec(q).dot(up)*vec(p).cross(uq) + vec(q).dot(vec(p).cross(up))*uq

def symbolic_swapped_curl_defect_certificate():
    """Universal polynomial certificate over a commutative scalar ring.

    By substitution this also holds over the repo's Complex3 scalar
    carrier, but this Python test is NOT an Agda kernel transport term.
    """
    p=S.symbols("p0:3");q=S.symbols("q0:3")
    up=S.symbols("u0:3");uq=S.symbols("v0:3")
    p,q,up,uq=map(vec,(p,q,up,uq))
    left=ordered_curl_residual(p,q,up,uq)+ordered_curl_residual(q,p,uq,up)
    right=vec(p).dot(up)*vec(q).cross(uq)+vec(q).dot(uq)*vec(p).cross(up)
    return all(S.expand(x)==0 for x in left-right)
