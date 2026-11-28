"""Literal cyclic-Golay -> mmgroup MOG Leech coordinate identification.

Use the Steiner S(5,8,24) incidence geometry rather than an arbitrary
quadratic-frame isomorphism. Source: Conway--Sloane, Curtis MOG,
Seysen mmgroup API/guide (Golay and Q_x0). DASHI weld retains actual
source sign corrections for the 12 Golay generators and 23-cycle.
"""
import argparse
from collections import defaultdict
from pathlib import Path
import json
from time import monotonic
from scripts.check_x369_concrete_leech_golay_glue import (
    golay, GENERATORS, membership, signed_action, cycle_action, require)
from scripts.check_x369_leech_discriminant_central_weld import (
    lattice_mod2_encode, action_columns, apply, solve, span, split_q, central_mul, lift)

MASK=(1<<24)-1


def points(x):return tuple(i for i in range(24) if x>>i&1)


def permute_mask(x,p):return sum(1<<p[i] for i in points(x))


def permutation(source,target):
    """Extend ordered umbral heptads by unique octad incidences."""
    so=sorted(x for x in source if x.bit_count()==8)
    to=sorted(x for x in target if x.bit_count()==8)
    require(len(source)==len(target)==4096 and len(so)==len(to)==759,'Golay code sizes')
    # Umbral heptad: six in one octad, one outside.
    def heptad(o):return points(o)[:6]+(next(i for i in range(24) if not o>>i&1),)
    known=dict(zip(heptad(so[0]),heptad(to[0])))
    rounds=[]
    while len(known)<24:
        mask=sum(1<<i for i in known)
        pairs=[]
        for x in so:
            k=x&mask
            if k.bit_count()<5:continue
            yk=sum(1<<known[i] for i in points(k))
            ys=[y for y in to if y&yk==yk]
            require(len(ys)==1,'unique target octad through 5 points')
            y=ys[0]
            require(all(bool(x>>i&1)==bool(y>>j&1) for i,j in known.items()),'partial incidence mismatch')
            pairs.append((x,y))
        a=defaultdict(list);b=defaultdict(list)
        for i in range(24):
            if i not in known:a[tuple(x>>i&1 for x,y in pairs)].append(i)
            if i not in known.values():b[tuple(y>>i&1 for x,y in pairs)].append(i)
        require(set(a)==set(b) and all(len(a[k])==len(b[k]) for k in a),'octad signature mismatch')
        new={a[k][0]:b[k][0] for k in a if len(a[k])==1}
        require(new,'umbral incidence did not determine remaining coordinates')
        rounds.append(dict(known_before=len(known),octads=len(pairs),new_points=len(new)))
        known.update(new)
    p=tuple(known[i] for i in range(24))
    require(len(set(p))==24 and {permute_mask(x,p) for x in source}==set(target),
            'full Golay coordinate equivalence')
    return p,rounds


def map_point(x,p):
    y=[0]*24
    for i,j in enumerate(p):y[j]=x[i]
    return tuple(y)


def actual(seconds):
    from mmgroup import GCode,MM,MMSpace,XLeech2,AutPL
    from importlib.metadata import version
    require(0<seconds<=90,'bounded actual source')
    deadline=monotonic()+seconds
    def budget():
        if monotonic()>=deadline:raise TimeoutError('actual coordinate weld budget')
    target={sum(1<<j for j in GCode(i).bit_list) for i in range(4096)}
    p,rounds=permutation(golay(),target)
    inv=tuple(p.index(i) for i in range(24))
    selected=[];binary=[];actual_labels=[];checks=0;seen=[]
    # The three genuine minimum-vector families span the lattice.
    # Include both two-point signs, all octad supports, odd family.
    indices=list(range(300,852))+list(range(852,49428,64))+list(range(49428,98580,24))
    for i in indices:
        budget()
        x=tuple(map(int,MMSpace.index_to_short('E',i)))
        require(len(x)==24 and sum(v*v for v in x)==32,'source short norm')
        v=map_point(x,inv)
        require(membership(v) is not None,'actual mapped short membership')
        b=lattice_mod2_encode(v)
        q=int(XLeech2(MMSpace.index_to_short_mod2('E',i)).ord)&MASK
        seen.append((i,b,q))
        if len(span(binary+[b]))>len(binary):
            binary.append(b);actual_labels.append(q);selected.append(i)
        if len(binary)==24:break
    require(len(binary)==len(span(actual_labels))==24,'full actual mod2 basis')
    bp=span(binary);qp=span(actual_labels)
    def forward(x):return apply(actual_labels,solve(bp,x))
    def backward(q):return apply(binary,solve(qp,q))
    for i,b,q in seen:
        require(forward(b)==q and backward(q)==b,'actual short coordinate square')
        checks+=1
    # Cross-check all families independent of selected basis.
    for i in (300,575,576,851,852,853,49427,49428,49429,98579):
        x=tuple(map(int,MMSpace.index_to_short('E',i)))
        b=lattice_mod2_encode(map_point(x,inv));q=int(XLeech2(MMSpace.index_to_short_mod2('E',i)).ord)&MASK
        require(forward(b)==q and backward(q)==b,'independent actual short alignment')
        checks+=1
    z=XLeech2(1<<24);one=XLeech2(0)
    frame=[XLeech2(forward(1<<i)) for i in range(24)]
    for i,g in enumerate(frame):
        require(g*g==one,'actual quadratic isotropy')
        for j,h in enumerate(frame):
            require(g*h==(z if (i+12)%24==j else one)*h*g,'actual polar isometry')
    def source(x,s):
        g=one
        for i in range(12,24):
            if x>>i&1:g=g*frame[i]
        for i in range(12):
            if x>>i&1:g=g*frame[i]
        return g*z if s else g
    def reopen(g):
        x=backward(int(g.ord)&MASK);b=source(x,0)
        require(g==b or g==b*z,'actual signed source inverse')
        return x,int(g!=b)
    for x in (0,1,4096,0xffffff,0xabcdef):
        for s in (0,1):
            require(reopen(source(x,s))==(x,s),'actual signed inverse')
            for y in (1,4096,0x123456):
                require(source(*central_mul((x,s),(y,1)))==source(x,s)*source(y,1),
                        'actual central product')
    actions=[]
    # Golay sign changes y_d and M24 coordinate permutation x_pi.
    # Choose actual lift by checking the complete coordinate square.
    from mmgroup import GcVector
    specs=[]
    for i,mask in enumerate(GENERATORS):
        m=permute_mask(mask,p)
        g=MM('y',GCode(GcVector(m)))
        specs.append(('golay-sign-'+str(i),lambda x,m=mask:signed_action(x,m),g))
    cycle=[p[(inv[j]+1)%23] if inv[j]<23 else p[23] for j in range(24)]
    specs.append(('cycle23',cycle_action,MM(AutPL(0,cycle))))
    for name,action,word in specs:
        budget()
        columns=action_columns(action)
        def actual_action(x,s,g):
            return reopen(XLeech2(g**-1*MM(source(x,s))*g))
        # Right/left permutation convention is explicitly checked;
        # choose an inverse word only if all 24 quotient columns agree.
        g=next((g for g in (word,word**-1) if
                all(actual_action(1<<i,0,g)[0]==columns[i] for i in range(24))),None)
        require(g is not None,'actual source action not coordinate aligned '+name)
        correction=sum(actual_action(1<<i,0,g)[1]<<i for i in range(24))
        for x in (0,1,4096,0xffffff,0xabcdef,0x123456):
            for s in (0,1):
                a,t=lift(columns,(x,s));t^=(x&correction).bit_count()%2
                require(actual_action(x,s,g)==(a,t),'actual lift sign correction '+name)
        actions.append(dict(name=name,word=str(g),binary_columns=columns,
                            linear_sign_correction=correction))
    return dict(status='actual_coordinate_aligned_Leech_Qx0',
        mmgroup_version=version('mmgroup'),permutation=p,inverse_permutation=inv,
        incidence_refinement=rounds,all_4096_codewords_equivalent=True,
        short_source_basis_indices=selected,concrete_binary_basis=binary,
        actual_binary_basis=actual_labels,actual_hyperbolic_frame=[int(q.ord) for q in frame],
        short_coordinate_checks=checks,actual_aligned_generator_lifts=actions,
        full_Co1_action_certified=False,original_neural_lattice_action_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=actual(a.seconds);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps(r,sort_keys=True,indent=2))

if __name__=='__main__':main()
