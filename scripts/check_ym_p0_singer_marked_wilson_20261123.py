#!/usr/bin/env python3
"""YM P0: one original 4D Wilson density, 1/F/G/FG, Singer signed k charts.

Exact finite Q8<=SU2 subgroup / 8 selected original gauge fields, NOT
continuous compact SU(N) Haar or an original CMP119 localized T identity.
Imports the already-owned 1024-link/1536-plaquette Q8 source fixture.
"""
from fractions import Fraction
from itertools import product
from check_ym_369_original_full1024_wilson_gauge_fibre_20261123 import (
    sites, original_bonds, original_plaquettes, coarse_bonds,
    pair, step, sign9, mul, inv,
)

def group_plaquette(field, site, a, b):
    # Same original positive-word order +a,+b,-a,-b (not commuting).
    A=field[(site,a)]
    B=field[(step(site,a),b)]
    C=inv(field[(step(site,b),a)])
    D=inv(field[(site,b)])
    return mul(mul(mul(A,B),C),D)

def trace(q):
    return 1 if q==0 else -1 if q==4 else 0

def source_field(seed):
    return {(s,d):
        (seed*(1+3*d)+sum((j+1)*(v+1)*(seed+j+1)
                            for j,v in enumerate(s))
         +5*d*s[(d+1)%4])%8
        for s,d in original_bonds}

def source_branch(site):
    return tuple(None if x%2==0 else (x-1)//2 for x in site)

def decode_zero_branch(signed,branch):
    return tuple(0 if v==-1 else 2 if v==1 else 1+2*b
                 for v,b in zip(signed[:4],branch))

assert all(decode_zero_branch(sign9(site),source_branch(site))==site
           for site in sites)

# Original RH #1533 Singer word matrix on 3x3 trit blocks.
G=((-1,-1,0),(0,-1,-1),(-1,-1,-1))
def mm(a,b):
    return tuple(tuple(sum(a[i][l]*b[l][j] for l in range(3))%3
                       for j in range(3)) for i in range(3))
powers=[]
m=((1,0,0),(0,1,0),(0,0,1))
for k in range(26):
    powers.append(m)
    m=mm(G,m)
assert m==powers[0] and len(set(powers))==26

def signed_chart(site,k):
    src=sign9(site); M=powers[k]
    return tuple((sum(M[i][j]*src[b+j] for j in range(3))+1)%3-1
                 for b in (0,3,6) for i in range(3))

def indexed_original_field(field,k,clock):
    # Distinguish physical clock/history t from Singer chart k.
    return {(clock,k,signed_chart(s,k),source_branch(s),d):v
            for (s,d),v in field.items()}

def recover_original_field(indexed,k,clock):
    return {(s,d):indexed[(clock,k,signed_chart(s,k),source_branch(s),d)]
            for s,d in original_bonds}

def original_weight(field):
    # Actual Wilson sum over all 1536 plaquette words at beta=log(2):
    # exp[-beta*sum(1 - ReTr/2)] = exactly rational 2^(-deficit).
    deficit=sum(1-trace(group_plaquette(field,s,a,b))
                for s,a,b in original_plaquettes)
    return Fraction(1,2**deficit)

# Two DISTINCT, DISJOINT original positive Wilson marked plaquettes;
# second is translated by two native lattice steps along fourth axis.
mark_F=((0,0,0,0),0,1)
mark_G=((0,0,0,2),0,1)
rows=[]
selected=[b for c,d in coarse_bonds for b in pair(c,d)]
spectators=set(original_bonds)-set(selected)
assert len(selected)==128 and len(set(selected))==128 and len(spectators)==896

for seed in range(1,9):
    field=source_field(seed)
    weight=original_weight(field)
    F=trace(group_plaquette(field,*mark_F))
    H=trace(group_plaquette(field,*mark_G))
    rows.append((weight,F,H))
    # Every original 4D positive link, *every* source plaquette,
    # original Z weight, two marks and their mixed coefficient.
    for k in range(26):
        chart=indexed_original_field(field,k,clock=7)
        assert len(chart)==1024
        decoded=recover_original_field(chart,k,clock=7)
        assert decoded==field
        assert original_weight(decoded)==weight
        assert (trace(group_plaquette(decoded,*mark_F)),
                trace(group_plaquette(decoded,*mark_G)))==(F,H)
        # Source canonical->F19 original 64 noncommutative pair labels;
        # its inverse is W V^-1, never swapped V W^-1.
        sorted_pairs={(c,d):(mul(field[a],field[b]),field[b])
                      for c,d in coarse_bonds for a,b in [pair(c,d)]}
        original_rebuilt=dict.fromkeys(original_bonds)
        for c,d in coarse_bonds:
            a,b=pair(c,d)
            W,V=sorted_pairs[(c,d)]
            original_rebuilt[a]=mul(W,inv(V))
            original_rebuilt[b]=V
        for s in spectators:original_rebuilt[s]=field[s]
        assert original_rebuilt==field

Z=sum((w for w,F,H in rows),Fraction())
ZF=sum((w*F for w,F,H in rows),Fraction())
ZG=sum((w*H for w,F,H in rows),Fraction())
ZFG=sum((w*F*H for w,F,H in rows),Fraction())
assert Z*ZFG!=ZF*ZG # selected ensemble: mixed mark not factorized

print("PASS 8 original finite fields x 26 RH Singer stages x 1024 original links")
print("PASS all actual 1536 original plaquette-derived Wilson weights & distinct F/G marks")
print("PASS one common rational Wilson Z, F, G, FG; nonfactorizing mixed mark")
print("PASS 64 noncommutative original R445/F19 pairs + 896 spectator bonds")
print("NOT CLAIMED: full continuous SU(N) Haar measure, CMP119 source T, UV W3, OS gap")
