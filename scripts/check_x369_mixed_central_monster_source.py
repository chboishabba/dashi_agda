"""Exact mixed binary/ternary central transport and actual Monster local ports.

DASHI weld of classical extraspecial groups, Seysen mmgroup Q_x0 and
Dietrich/Lee/Pisani/Popiel 3B source words (existing source symplectic
basis owner). Not an embedding of their direct product into Monster.
No characteristic-zero FLM identification is inferred from modular action.
"""
import argparse
from itertools import product
import json
from pathlib import Path
from scripts.check_x369_leech_discriminant_central_weld import (
    leech_binary, central_mul, apply, span, solve, split_q)


def require(ok,msg):
    if not ok:raise ValueError(msg)


def crt(b,t):
    require(b in (0,1) and t in (0,1,2),'invalid residues')
    return (3*b+4*t)%6


def split6(x):
    require(type(x) is int and 0<=x<6,'invalid mixed phase')
    return x%2,x%3


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def mul3(x,y):
    a,b,t=x;c,d,u=y
    return tuple((i+j)%3 for i,j in zip(a,c)),tuple((i+j)%3 for i,j in zip(b,d)),(t+u+dot(a,d))%3


def encode(binary,ternary):
    x,s=binary;a,b,t=ternary
    require(type(x) is int and 0<=x<2**24 and s in (0,1),'binary point')
    require(len(a)==len(b)==6 and all(v in (0,1,2) for v in (*a,*b)),'ternary point')
    lo=tuple((x>>i)&1 for i in range(12));hi=tuple((x>>(i+12))&1 for i in range(12))
    return (tuple(crt(lo[i],a[i]) for i in range(6)),
            tuple(crt(hi[i],b[i]) for i in range(6)),lo[6:],hi[6:],crt(s,t))


def decode(m):
    a,b,c,d,z=m
    require(len(a)==len(b)==len(c)==len(d)==6 and
            all(type(v) is int and v in (0,1) for v in (*c,*d)),'extra binary pairs')
    A=[split6(v) for v in a];B=[split6(v) for v in b];s,t=split6(z)
    x=sum(v<<i for i,v in enumerate(tuple(v[0] for v in A)+c+tuple(v[0] for v in B)+d))
    return (x,s),(tuple(v[1] for v in A),tuple(v[1] for v in B),t)


def mixed_mul(x,y):
    decode(x);decode(y)
    a,b,c,d,z=x;e,f,g,h,w=y
    add=lambda x,y,p:tuple((i+j)%p for i,j in zip(x,y))
    return add(a,e,6),add(b,f,6),add(c,g,2),add(d,h,2),(z+w+dot(a,f)+3*dot(c,h))%6


def certificate():
    # Each matched pair has 6^3 states. Check both projections and
    # multiplication for every pair of elements of that one-pair group.
    n=0
    for a,b,z in product(range(6),repeat=3):
        for c,d,w in product(range(6),repeat=3):
            require(split6((z+w+a*d)%6)==tuple(
                (z%p+w%p+(a%p)*(d%p))%p for p in (2,3)),'CRT cocycle')
            require(split6((a+c)%6)==tuple((a+c)%p for p in (2,3)),'CRT addition')
            require(split6((b+d)%6)==tuple((b+d)%p for p in (2,3)),'CRT addition')
            n+=1
    # A mixed packet has six shared pairs and six retained binary pairs.
    # Bilinearity and CRT identity on each pair establish the full law.
    zero3=((0,)*6,(0,)*6,0)
    for x in (0,1,4096,0xffffff,0x123456):
        for s in (0,1):
            for t in (0,1,2):
                y=((1,2,0,1,2,0),(2,0,1,2,0,1),t)
                v=encode((x,s),y)
                require(decode(v)==((x,s),y),'mixed inverse')
                for k in (0,1,4096,0xffffff):
                    w=encode((k,1),zero3)
                    require(decode(mixed_mul(v,w))==(central_mul((x,s),(k,1)),mul3(y,zero3)),
                            'full mixed law')
    leech_cols,_=leech_binary()
    return dict(status='mixed_central_CRT_exact',binary_order=2**25,ternary_order=3**13,
                product_order=2**25*3**13,shared_mod6_pairs=6,retained_binary_pairs=6,
                one_pair_exhaustive_products=n,centre_order=6,
                binary_lattice_hyperbolic_frame=list(leech_cols),
                literal_binary_ternary_isomorphism=False,
                direct_product_embedded_in_monster=False,
                original_flm_action_certified=False)


def actual_binary():
    """Chosen quadratic isometry from concrete Leech frame to actual Q_x0.
    This is an exact central group isomorphism, not a standard-coordinate
    Golay permutation or an intertwiner for all Co1 lattice automorphisms.
    """
    from mmgroup import XLeech2, MM, MMV
    from importlib.metadata import version
    one=XLeech2(0);z=XLeech2(1<<24)
    A=[XLeech2(1<<i) for i in range(12)]
    B=[XLeech2(1<<(12+i)) for i in range(12)]
    require(z*z==one and z!=one,'actual Qx0 central order')
    for i in range(12):
        require(A[i]*A[i]==B[i]*B[i]==one,'actual hyperbolic isotropy')
        for j in range(12):
            require(A[i]*A[j]==A[j]*A[i] and B[i]*B[j]==B[j]*B[i],
                    'actual isotropic commutation')
            require(A[i]*B[j]==(z if i==j else one)*B[j]*A[i],
                    'actual binary Weyl commutation')
    def to_source(x,s):
        require(0<=x<2**24 and s in (0,1),'binary coordinate')
        w=one
        for i in range(12):
            if x>>(12+i)&1:w=w*B[i]
        for i in range(12):
            if x>>i&1:w=w*A[i]
        return w*z if s else w
    def from_source(w):
        x=int(w.ord)&0xffffff
        v=to_source(x,0)
        require(w==v or w==v*z,'actual source inverse')
        return x,int(w!=v)
    for x in (0,1,4096,4097,0x123456,0xffffff):
        for s in (0,1):
            require(from_source(to_source(x,s))==(x,s),'Qx0 inverse')
            for y in (1,4096,0xabcdef):
                require(to_source(*central_mul((x,s),(y,1)))==to_source(x,s)*to_source(y,1),
                        'Qx0 actual multiplication')
    mz=MM(z)
    require(mz.order()==2 and mz.chi_G_x0()[0]==275,'actual Monster 2B recognition')
    # Actual weight-two modular representation; sign projector in F7.
    V=MMV(7);samples=0;checks=0
    for label in [('A',0,0),('B',1,0),('T',0,0),('X',0,0),('Y',0,0),('Z',0,0)]:
        v=V(*label);w=4*(v-v*mz)
        require(w*mz==6*w,'actual 2B sign projector')
        if w==0*w:continue
        samples+=1
        for i in range(12):
            a,b=MM(A[i]),MM(B[i])
            require((w*a)*b==6*((w*b)*a),'actual modular V2 Weyl phase')
            checks+=1
    require(samples>0,'no actual nonzero binary phase probes')
    return dict(mmgroup_version=version('mmgroup'),center_word=str(mz),
                translation_words=[str(MM(a)) for a in A],modulation_words=[str(MM(b)) for b in B],
                actual_2B_character=275,actual_binary_group_relations=True,
                actual_binary_inverse=True,nonzero_modular_v2_samples=samples,
                modular_v2_weyl_checks=checks,concrete_standard_coordinate_alignment=False,
                full_Co1_intertwining=False)


def actual():
    binary=actual_binary()
    # Reuse the original 3B source-word producer; its normal order is
    # A^old_a B^old_b, so choose old_a=b, old_b=a for c=a dot b'.
    import sys
    # Existing source producer imports its companion by script-local name.
    sys.path.insert(0,str(Path(__file__).resolve().parent))
    from scripts.monster_3b_mmgroup_source_symplectic_basis import run
    manifest,receipt=run()
    from mmgroup import MM
    A=[MM(w) for w in manifest['translation_words']]
    B=[MM(w) for w in manifest['modulation_words']]
    z=MM(manifest['center_word'])
    def to_source(x):
        a,b,t=x;w=z**0
        for g,k in zip(A,b):w=w*g**k
        for g,k in zip(B,a):w=w*g**k
        return w*z**t
    for i in range(6):
        for j in range(6):
            a=tuple(int(k==i) for k in range(6));b=tuple(int(k==j) for k in range(6))
            zero=(0,)*6;x=(a,zero,0);y=(zero,b,0)
            require(to_source(mul3(x,y))==to_source(x)*to_source(y),'actual 3B normal order')
    return dict(binary=binary,ternary_manifest=manifest,ternary_source_receipt=receipt,
                actual_ternary_coordinate_order='original A^b B^a z^t',
                actual_local_source_attachments=True,
                independent_actual_monster_actions=True,
                direct_product_embedded_in_monster=False,
                full_original_flm_action_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--actual',action='store_true')
    p.add_argument('--output',type=Path);a=p.parse_args()
    out=certificate()
    if a.actual:out['actual_local_sources']=actual()
    result=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if a.output:
        with a.output.open('x') as f:f.write(result)
    print(result,end='')


if __name__=='__main__':main()
