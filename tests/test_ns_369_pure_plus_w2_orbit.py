"""Exact R734 pure-plus witness across physical NS369 three-axis C3 rotations.

NS369's finite sign fibre and oriented cross structure are already source
owners; the finite quotient is NOT a Rayleigh coercivity or W2 estimate.
Original helical triad mathematics is Waleffe (1992); these exact same-
physical-source orbit checks are DASHI's source-specific regression.
"""
from collections import defaultdict
from functools import lru_cache
import sympy as S
I=S.I
P=(1,0,0); Q=(0,1,2); K=(1,1,2)
SEEDS={P:(0,1,1),Q:(1,0,0),K:(1,-1,0)}
def n2(m):return sum(a*a for a in m)
def neg(m):return tuple(-a for a in m)
def rotate(m,j):return tuple(m[(i+j)%3] for i in range(3))
def sign(m):return tuple(1 if x>0 else -1 if x<0 else 0 for x in m)
def dyadic_weight(m):return 1 << (max(map(abs,m))-1).bit_length()
def hel(m,v,sigma):
    return (v+sigma*I*S.Matrix(m).cross(v)/S.sqrt(n2(m)))/2
def field(j):
    u={rotate(m,j):hel(rotate(m,j),S.Matrix(rotate(v,j)),+1)
       for m,v in SEEDS.items()}
    u.update({neg(m):S.conjugate(v) for m,v in list(u.items())})
    return u
def projected_NS(u,N=2):
    raw=defaultdict(lambda:S.zeros(3,1))
    for a,ua in u.items():
        for b,ub in u.items():
            mode=tuple(a[i]+b[i] for i in range(3))
            raw[mode]+=S.Matrix(b).dot(ua)*ub
    out={}
    for m,v in raw.items():
        if n2(m)==0 or max(map(abs,m))>N:continue
        kv=S.Matrix(m);out[m]=-I*(v-kv*kv.dot(v)/n2(m))
    return out
@lru_cache(None)
def observables(j):
    u=field(j);n=projected_NS(u)
    norm=lambda v:S.simplify((S.conjugate(v).T*v)[0])
    E=S.simplify(sum((dyadic_weight(m)*norm(v) for m,v in u.items()),S.Integer(0)))
    D=S.simplify(sum((dyadic_weight(m)*n2(m)*norm(v) for m,v in u.items()),S.Integer(0)))
    P=S.simplify(S.expand_complex(sum((
        2*dyadic_weight(m)*S.re((S.conjugate(v).T*n.get(m,S.zeros(3,1)))[0])
        for m,v in u.items()),S.Integer(0))))
    return E,D,P

def test_same_physical_observables_three_cyclic_rotations():
    Pexpected=(5+S.sqrt(5)-S.sqrt(30))/10
    for j in (0,1,2):
        E,D,prod=observables(j)
        assert E==8 and D==36 and S.simplify(prod-Pexpected)==0
        for m,v in field(j).items():
            assert S.simplify(S.Matrix(m).dot(v))==0
            assert S.simplify(hel(m,v,-1))==S.zeros(3,1)

def test_three_distinct_ternary_sign_triads():
    signatures=[]
    for j in range(3):
        a,b,c=[rotate(m,j) for m in (P,Q,K)]
        assert tuple(a[i]+b[i] for i in range(3))==c
        signature=tuple(sign(m) for m in (a,b,c))
        assert len(signature)==3
        assert all(len(v)==3 and all(z in (-1,0,1) for z in v)
                   for v in signature)
        signatures.append(signature)
    assert len(set(signatures))==3

def test_amplitude_scaling_preserves_369_class_but_not_w2_margin():
    for a in (512,1024,2048):
        for j in range(3):
            E,D,P=observables(j)
            assert S.simplify(a*a*(a*P-2*D)>0) is S.true
            u=field(j)
            scaled={m:a*v for m,v in u.items()}
            assert set(scaled)==set(u)
            assert tuple(sign(m) for m in scaled)==tuple(sign(m) for m in u)

def test_improper_reflection_changes_helicity_sector():
    v=S.Matrix((0,1,1));R=S.diag(-1,1,1)
    assert R.det()==-1
    positive=hel(P,v,+1);reflected=tuple(R*S.Matrix(P))
    assert S.simplify(R*positive-hel(reflected,R*v,-1))==S.zeros(3,1)
    assert S.simplify(R*positive-hel(reflected,R*v,+1))!=S.zeros(3,1)

def test_ternary_sign_fibre_does_not_contain_frequency_norm_or_amplitude():
    assert sign((1,0,0))==sign((100,0,0))
    assert n2((1,0,0))!=n2((100,0,0))
    assert dyadic_weight((1,0,0))!=dyadic_weight((100,0,0))

def test_all_six_axis_permutations_include_opposite_helicity_same_369_sign_class():
    # All SIX physical orthogonal axis permutations preserve the Galerkin
    # NS equation and the max-coordinate dyadic critical weight.
    # Improper transformations det=-1 exchange true curl helicity
    # polarity. The coordinate-SIGN quotient records only THREE
    # signatures: each is shared by one proper and one improper orbit
    # member. Thus it cannot encode Waleffe polarization by itself.
    from itertools import permutations
    orbit=[]
    for permutation in permutations(range(3)):
        inversion_count=sum(permutation[i]>permutation[j]
                            for i in range(3) for j in range(i+1,3))
        parity=1 if inversion_count%2==0 else -1
        rotate_axes=lambda m:tuple(m[j] for j in permutation)
        u={rotate_axes(m):S.Matrix(rotate_axes(v))
           for m,v in field(0).items()}
        forcing=projected_NS(u)
        norm=lambda v:S.simplify((S.conjugate(v).T*v)[0])
        E=S.simplify(sum((dyadic_weight(m)*norm(v) for m,v in u.items()),S.Integer(0)))
        D=S.simplify(sum((dyadic_weight(m)*n2(m)*norm(v) for m,v in u.items()),S.Integer(0)))
        production=S.simplify(S.expand_complex(sum((
            2*dyadic_weight(m)*S.re((S.conjugate(v).T*
                forcing.get(m,S.zeros(3,1)))[0])
            for m,v in u.items()),S.Integer(0))))
        assert E==8 and D==36 and S.simplify(production-observables(0)[2])==0
        for m,v in u.items():
            assert S.simplify(hel(m,v,-parity))==S.zeros(3,1)
        signature=tuple(sign(rotate_axes(m)) for m in (P,Q,K))
        orbit.append((signature,parity))
    assert len(orbit)==6
    assert len({sig for sig,_ in orbit})==3
    assert all({p for sig,p in orbit if sig==key}=={-1,+1}
               for key in {sig for sig,_ in orbit})
