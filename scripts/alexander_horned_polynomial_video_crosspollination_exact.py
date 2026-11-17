#!/usr/bin/env python3
"""Independent exact finite tests for video-root/horned-C3 cross-pollination.

Owners: S3/TernaryEndomorphismConjugacyExact, Hatcher classical binary
meridians (Alexander 1924/Hatcher Example 2B.2), #1244 native end and
fibre actions, #1414 braid/S3/Spin (independent *branch-only* donor),
#1275 Heaps and #1407 13/27 orbits. No result proves the ambient
wild embedding, actual analytic polynomial monodromy, Monster 3B or RH.
Agda source is KERNEL-PENDING; no CI implied.
"""
from itertools import product, permutations

def comp(a,b):
    return tuple(a[b[i]] for i in range(3))

def inv(a):
    return tuple(a.index(i) for i in range(3))

def comm(a,b):
    return comp(comp(comp(a,b),inv(a)), inv(b))

def orbits(points, involution):
    unseen=set(points)
    sizes=[]
    while unseen:
        x=next(iter(unseen))
        orbit={x, involution(x)}
        assert all(involution(y) in orbit for y in orbit)
        sizes.append(len(orbit))
        unseen-=orbit
    return tuple(sorted(sizes))

def main():
    ident=(0,1,2)
    r=(1,2,0)
    rinverse=(2,0,1)
    reflection=(2,1,0)
    s3=list(permutations(range(3)))
    c3=(ident,r,rinverse)
    assert len(s3)==6
    assert all(comm(a,b) in c3 for a,b in product(s3,repeat=2))
    assert all(comm(a,b)==ident for a,b in product(c3,repeat=2))
    assert comp(comp(reflection,r),reflection)==rinverse

    # Intrinsic native balanced end *address* at depth 2:
    # sector + 2 trits, NOT the two binary Hatcher child choices.
    x27=list(product(range(3),repeat=3))
    negate=lambda t:2-t
    global_sign=lambda x:tuple(map(negate,x))
    internal_sign=lambda x:(x[0],negate(x[1]),negate(x[2]))
    assert len(x27)==27
    assert all(global_sign(global_sign(x))==x for x in x27)
    assert all(internal_sign(internal_sign(x))==x for x in x27)
    global_fixed=[x for x in x27 if global_sign(x)==x]
    internal_fixed=[x for x in x27 if internal_sign(x)==x]
    assert global_fixed==[(1,1,1)]
    assert internal_fixed==[(c,1,1) for c in range(3)]
    assert orbits(x27,global_sign).count(2)==13
    assert len(orbits(x27,global_sign))==14
    assert orbits(x27,internal_sign).count(2)==12
    assert len(orbits(x27,internal_sign))==15

    # Two B-fixed points would have to inject into A's only fixed
    # point under an intertwining injection: impossible.
    assert len(internal_fixed)>len(global_fixed)

    # Constructor-level native address/code bijection: explicitly
    # the 27 T×T×T triples, not equality of their semantic roles.
    code=lambda x:x
    decode=lambda x:x
    assert all(decode(code(x))==x for x in x27)
    assert all(code(decode(x))==x for x in x27)

    # Heaps equality class is invariant under global S3 relabelling
    # but not under independent local S3 values.
    seed=(0,0,0)
    local=(2,0,0)
    assert seed[:2]==(0,0) and local[:2]!=(0,0)
    assert all((perm[a]==perm[b]) == (a==b)
               for perm in s3 for a,b in product(range(3),repeat=2))
    assert all((p[seed[0]]==p[seed[1]]) ==
               (seed[0]==seed[1]) for p in s3)
    assert len({seed[0],seed[1]})==1
    assert len({local[0],local[1]})==2

    # True recurrence: source Hatcher group remains binary, not 3^n.
    assert [3*2**n for n in range(6)] == [3,6,12,24,48,96]
    assert [3*3**n for n in range(6)] == [3,9,27,81,243,729]
    assert 3**27 == 7625597484987
    assert 3**(3**3) == 3**27
    assert 3*(3**27) == 22876792454961

    # Genuine 243-versus-125 map reversal and complete kernel.
    fields5=list(product(range(3),repeat=5))
    selectors=list(product(range(5),repeat=3))
    assert len(fields5)==243 and len(selectors)==125
    selector=(0,1,2)
    readout_fibres={}
    for f in fields5:
        snapshot=tuple(f[i] for i in selector)
        readout_fibres[snapshot]=readout_fibres.get(snapshot,0)+1
    assert len(readout_fibres)==27
    assert set(readout_fibres.values())=={9}
    neutral_kernel={f for f in fields5 if f[:3]==(0,0,0)}
    assert neutral_kernel == {(0,0,0,a,b)
                              for a,b in product(range(3),repeat=2)}

    # The three-strand full twist has trivial S3 endpoint, yet
    # exponent sum 6 and hence nonzero modulo 7.
    s0=(1,0,2)
    s1=(0,2,1)
    word=(s0,s1)*3
    endpoint=ident
    for crossing in word:
        endpoint=comp(endpoint,crossing)
    assert endpoint==ident and len(word)==6 and len(word)%7==6
    assert comp(comp(s0,s1),s0)==comp(comp(s1,s0),s1)

    print("PASS: S3->C3->1, sector D3, 27 chart, 13/27 vs 15-orbit no-go,")
    print("      local-vs-global Heaps, 3^27, binary/ternary separation,")
    print("      B3 full twist exponent mod7=6 with S3 identity endpoint")
    print("      3^5=243 vs 5^3=125, 27 readouts each with exact 9-field kernel")
    print("NO PROMOTION: no actual wild geometry, Pickover radian sign, RH,")
    print("              Monster 3B equivalence or Agda kernel proof")

if __name__=="__main__":
    main()
