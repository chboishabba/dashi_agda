"""Concrete common-glue discriminant and Leech mod-2 central extension.

Classical even-lattice discriminant form, Golay Leech and extraspecial
2-group constructions retain their original attribution. DASHI weld:
actual accepted integer bases, explicit inverse coordinates, and lifts
of the certified Golay sign/cyclic lattice actions. Not Monster/FLM
source action or identification with the separate F3 Heisenberg group.
"""
import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
from sympy import Matrix

from scripts.check_x369_concrete_leech_golay_glue import (
    basis, basis_inverse, membership, signed_action, cycle_action, GENERATORS, require)
from scripts.check_x369_three_e8_leech_common_glue import geometry, integer, vector


def bits(xs):
    return sum((int(x)%2)<<i for i,x in enumerate(xs))


def unpack(x,n):
    require(type(x) is int and 0<=x<1<<n,'binary coordinate outside carrier')
    return Matrix([(x>>i)&1 for i in range(n)])


def parity(x):return x.bit_count()%2


def span(columns):
    """GF2 elimination retaining the original generator coordinates."""
    piv={}
    for j,x in enumerate(columns):
        y=x;w=1<<j
        while y:
            k=y.bit_length()-1
            if k in piv:
                a,b=piv[k];y^=a;w^=b
            else:
                piv[k]=(y,w);break
    return piv


def solve(piv,x):
    w=0
    while x:
        k=x.bit_length()-1
        require(k in piv,'binary vector outside selected span')
        a,b=piv[k];x^=a;w^=b
    return w


def apply(columns,x):
    require(type(x) is int and 0<=x<1<<len(columns),'binary input width')
    out=0
    for i,v in enumerate(columns):
        if x>>i&1:out^=v
    return out


def independent_indices(columns):
    out=[];piv={}
    for i,x in enumerate(columns):
        y=x
        while y:
            k=y.bit_length()-1
            if k in piv:y^=piv[k]
            else:piv[k]=y;out.append(i);break
    return out


@lru_cache(maxsize=1)
def discriminant():
    _,c,ci,sides=geometry()
    a=sides['three_e8'][0];b=sides['golay_leech'][0]
    # For a member of I*, 2x is in I. Verify this on the literal dual basis.
    dual=8*ci.T
    integer(2*ci*dual)
    require((c.T*c/8).det()==2**24,'common discriminant order')
    def label(x):return bits(integer(2*ci*x))
    ua=independent_indices([label(a[:,i]) for i in range(24)])
    vb=independent_indices([label(b[:,i]) for i in range(24)])
    require(len(ua)==len(vb)==12,'glue subgroup ranks')
    u=a[:,ua];v=b[:,vb]
    pairing=integer(u.T*v/4)
    pcols=[bits(pairing[:,j]) for j in range(12)]
    pinv=span(pcols)
    require(len(pinv)==12,'glue pairing degenerate')
    # Pick the dual basis on the Leech side; the two isotropic
    # complementary subgroups now have cross pairing delta_ij.
    v=v*Matrix.hstack(*(unpack(solve(pinv,1<<j),12) for j in range(12)))
    p=integer(u.T*v/4)
    require(all(int(p[i,j])%2==int(i==j) for i in range(12) for j in range(12)),
            'dual glue pairing mismatch')
    for x in (u,v):
        gram=x.T*x/8
        require(all(t.q==1 for t in gram) and all(gram[i,i]%2==0 for i in range(12)),
                'glue subgroup not isotropic')
    reps=u.row_join(v)
    labels=[label(reps[:,i]) for i in range(24)]
    piv=span(labels)
    require(len(piv)==24,'not a full discriminant basis')
    return c,ci,reps,piv,tuple(ua),tuple(vb)


def discriminant_split(point):
    """Rational scaled ambient point in I* -> common integer + 24 bits."""
    c,ci,reps,piv,_,_=discriminant()
    x=Matrix(point)
    require(x.shape==(24,1),'ambient dimension')
    integer(c.T*x/8)
    label=solve(piv,bits(integer(2*ci*x)))
    z=integer(ci*(x-reps*unpack(label,24)))
    require(c*z+reps*unpack(label,24)==x,'common inverse')
    return vector(z),label


def discriminant_stitch(z,label):
    c,_,reps,_,_,_=discriminant()
    require(len(z)==24 and all(type(t) is int for t in z),'common integer coordinates')
    x=c*Matrix(z)+reps*unpack(label,24)
    require(discriminant_split(x)==(tuple(z),label),'discriminant inverse')
    return tuple(x)


def split_q(x):
    unpack(x,24)
    return parity((x&4095)&(x>>12))


@lru_cache(maxsize=1)
def leech_binary():
    b=Matrix(basis());g=integer(b.T*b/8)
    rows=[bits(g[i,:]) for i in range(24)]
    diag=bits([g[i,i]//2 for i in range(24)])
    def bil(x,y):
        return parity(sum((rows[i]&y).bit_count() for i in range(24) if x>>i&1))
    def q(x):
        inds=[i for i in range(24) if x>>i&1]
        return (parity(x&diag)+sum(int(g[i,j]) for i in inds for j in inds if j<i))%2
    work=[1<<i for i in range(24)];pairs=[]
    while work:
        e=next((x for x in work if q(x)==0),None)
        if e is None:
            e=next((x^y for x,y in combinations(work,2) if q(x^y)==0),None)
        require(e is not None,'anisotropic terminal block')
        f=next((x for x in work if bil(e,x)),None)
        require(f is not None,'degenerate polar pairing')
        if q(f):f^=e
        require(q(e)==q(f)==0 and bil(e,f)==1,'invalid hyperbolic plane')
        pairs.append((e,f))
        residual=[x^(e if bil(x,f) else 0)^(f if bil(x,e) else 0) for x in work]
        work=[residual[i] for i in independent_indices(residual)]
    cols=tuple(e for e,f in pairs)+tuple(f for e,f in pairs)
    piv=span(cols)
    require(len(pairs)==12 and len(piv)==24,'not a full hyperbolic frame')
    for i,x in enumerate(cols):
        require(q(x)==0,'nonisotropic hyperbolic basis')
        for j,y in enumerate(cols):
            require(bil(x,y)==int((i+12)%24==j),'hyperbolic Gram mismatch')
    return cols,piv


def lattice_mod2_encode(point):
    require(membership(tuple(point)) is not None,'not a Leech point')
    c=integer(basis_inverse()*Matrix(point))
    return solve(leech_binary()[1],bits(c))


def lattice_mod2_reopen(label,even_coordinates):
    require(len(even_coordinates)==24 and all(type(x) is int for x in even_coordinates),
            'even lattice residual coordinates required')
    v=apply(leech_binary()[0],label)
    p=vector(basis()*(unpack(v,24)+2*Matrix(even_coordinates)))
    require(lattice_mod2_encode(p)==label,'Leech mod2 inverse')
    return p


def lattice_mod2_split(point):
    x=tuple(point);label=lattice_mod2_encode(x)
    c=integer(basis_inverse()*Matrix(x))
    r=integer((c-unpack(apply(leech_binary()[0],label),24))/2)
    require(lattice_mod2_reopen(label,vector(r))==x,'Leech retained even residual')
    return label,vector(r)


def cocycle(x,y):
    unpack(x,24);unpack(y,24)
    return parity((x&4095)&(y>>12))


def central_mul(left,right):
    x,s=left;y,t=right
    require(s in (0,1) and t in (0,1),'binary central sign')
    return x^y,s^t^cocycle(x,y)


def action_columns(action):
    out=[]
    for j in range(24):
        p=lattice_mod2_reopen(1<<j,(0,)*24)
        out.append(lattice_mod2_encode(action(p)))
    require(len(span(out))==24,'noninvertible lattice mod2 action')
    for i,a in enumerate(out):
        require(split_q(a)==0,'action does not preserve quadratic form')
        for j,b in enumerate(out):
            require(cocycle(a,b)^cocycle(b,a)==int((i+12)%24==j),
                    'action does not preserve polar form')
    return tuple(out)


def lift_correction(columns,x):
    unpack(x,24)
    # c(Ax,Ay)+c(x,y) is symmetric alternating, so it is the
    # polarization of this explicit quadratic 1-cochain.
    inds=[i for i in range(24) if x>>i&1]
    return sum(cocycle(columns[i],columns[j])^cocycle(1<<i,1<<j)
               for i,j in combinations(inds,2))%2


def lift(columns,element):
    x,s=element
    return apply(columns,x),s^lift_correction(columns,x)


def certificate():
    c,ci,reps,piv,ua,vb=discriminant()
    for j in range(24):
        z,label=discriminant_split(reps[:,j])
        require(z==(0,)*24 and label==1<<j,'discriminant basis inverse')
    # Bilinear form + isotropic basis proves the quadratic identity on
    # every 24-bit vector, not just enumeration of a sample.
    checks=0
    cols,_=leech_binary()
    actions=[('golay-sign-'+str(i),lambda p,m=m:signed_action(p,m))
             for i,m in enumerate(GENERATORS)]+[('cycle23',cycle_action)]
    action_rows=[]
    for name,action in actions:
        a=action_columns(action)
        for i in range(24):
            for j in range(24):
                x,y=(1<<i,0),(1<<j,0)
                require(lift(a,central_mul(x,y))==central_mul(lift(a,x),lift(a,y)),
                        'central cocycle lift basis mismatch')
                checks+=1
        action_rows.append(dict(name=name,binary_columns=list(a)))
    for label in (0,1,4096,4097,(1<<24)-1):
        x=discriminant_stitch((0,)*24,label)
        require((sum(t*t for t in x)/8)%2==split_q(label),'scaled discriminant q mismatch')
        p=lattice_mod2_reopen(label,tuple(i-12 for i in range(24)))
        require(lattice_mod2_split(p)==(label,tuple(i-12 for i in range(24))),
                'mod2 even residual inverse')
        require(sum(t*t for t in p)//16%2==split_q(label),'Leech mod2 quadratic mismatch')
    return dict(status='concrete_binary_quadratic_and_central_extension_weld',
        common_discriminant_order=2**24,complementary_glue_dimensions=[12,12],
        three_e8_basis_indices=ua,leech_basis_indices=vb,
        discriminant_hyperbolic_representatives=[list(map(int,reps[:,j])) for j in range(24)],
        leech_mod2_hyperbolic_columns=cols,leech_mod2_order=2**24,
        isotropic_count_including_zero=2**23+2**11,anisotropic_count=2**23-2**11,
        central_extension_order=2**25,actual_lattice_generator_lifts=action_rows,
        generator_pair_checks=checks,full_group_relations_or_canonical_lift_certified=False,
        original_neural_lattice_action_certified=False,
        original_monster_flm_action_certified=False,agda_kernel_checked=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=json.dumps(certificate(),indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(result)
    print(result,end='')


if __name__=='__main__':main()
