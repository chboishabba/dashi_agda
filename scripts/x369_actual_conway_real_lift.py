"""Real Leech/Co1 action for arbitrary actual G_x0 word, with sign retained.

Reuse accepted literal coordinate alignment, not an arbitrary orthogonal
frame. Lift the mod-2 images of a fixed real basis of short vectors:
the two minimum representatives differ only by sign. Inner products
recover every relative sign via a connected nonorthogonality graph
(Seysen, mmgroup API, Computing in G_x0). The overall sign is a
section choice, not a canonical Co1 -> Co0 homomorphism.
"""
import argparse
import hashlib
import json
from pathlib import Path
from time import monotonic
from sympy import Matrix
from scripts.check_x369_concrete_leech_golay_glue import basis,membership
from scripts.check_x369_leech_discriminant_central_weld import (
    lattice_mod2_encode,lattice_mod2_reopen,span,solve,apply,central_mul,lift,require)
from scripts.x369_actual_leech_coordinate_alignment import map_point

MASK=(1<<24)-1


def short_frame():
    cols=[]
    for i in range(1,24):
        v=[0]*24;v[0]=4;v[i]=4;cols.append(tuple(v))
    v=[0]*24;v[0]=4;v[1]=-4;cols.append(tuple(v))
    require(all(membership(v) and sum(x*x for x in v)==32 for v in cols),'source short frame')
    b=Matrix.hstack(*(Matrix(v) for v in cols))
    require(b.det()!=0,'real short frame rank')
    return b


def orient(source,target):
    require(source.shape==target.shape==(24,24),'short frame shape')
    S=source.T*source;T=target.T*target
    require(all(abs(S[i,j])==abs(T[i,j]) for i in range(24) for j in range(24)),
            'short-image Gram magnitude')
    signs={0:1}
    while len(signs)<24:
        n=len(signs)
        for i in tuple(signs):
            for j in range(24):
                if S[i,j]==0:continue
                s=int(S[i,j]/T[i,j])*signs[i]
                if j in signs:require(signs[j]==s,'relative sign cycle mismatch')
                else:signs[j]=s
        require(len(signs)>n,'short frame nonorthogonality graph disconnected')
    v=Matrix.hstack(*(target[:,i]*signs[i] for i in range(24)))
    require(v.T*v==S,'oriented exact Gram')
    return v


def canonical(M):
    k=next(x for x in M if x)
    return M if k>0 else -M


def signed_composition(first,second,combined):
    # Column convention: applying first and then second gives second*first.
    x=second*first
    require(x==combined or x==-combined,'actual Conway section composition')
    return int(x!=combined)


class Alignment:
    def __init__(self,r):
        from mmgroup import XLeech2
        require(r['status']=='actual_coordinate_aligned_Leech_Qx0' and
                r['all_4096_codewords_equivalent'] is True,'accepted literal source alignment')
        self.p=tuple(r['permutation']);self.inv=tuple(r['inverse_permutation'])
        require(sorted(self.p)==list(range(24)) and self.inv==tuple(self.p.index(i) for i in range(24)),
                'source permutation inverse')
        self.cols=tuple(r['actual_hyperbolic_frame'])
        require(len(self.cols)==24 and len(span([x&MASK for x in self.cols]))==24,'source quadratic frame')
        self.piv=span([x&MASK for x in self.cols])
        self.frame=tuple(XLeech2(x) for x in self.cols)
        self.one=XLeech2(0);self.z=XLeech2(1<<24)
        for i,g in enumerate(self.frame):
            require(g*g==self.one,'source frame isotropy')
            for j,h in enumerate(self.frame):
                require(g*h==(self.z if (i+12)%24==j else self.one)*h*g,'source frame polarization')

    def source(self,x,s=0):
        require(type(x) is int and 0<=x<2**24 and s in (0,1),'source signed coordinates')
        w=self.one
        for i in (*range(12,24),*range(12)):
            if x>>i&1:w=w*self.frame[i]
        return w*self.z if s else w

    def reopen(self,g):
        x=solve(self.piv,int(g.ord)&MASK);w=self.source(x)
        require(g==w or g==w*self.z,'source normal form inverse')
        return x,int(g!=w)

    def moved(self,g,x,s=0):
        from mmgroup import MM,XLeech2
        return self.reopen(XLeech2(g**-1*MM(self.source(x,s))*g))

    def short_image(self,g,v):
        from mmgroup import MMSpace,XLeech2
        x=lattice_mod2_encode(v)
        y,_=self.moved(g,x)
        q=XLeech2(int(self.source(y).ord)&MASK)
        idx=MMSpace.index_to_linear(q)
        require(300<=idx<98580,'actual short vector image')
        w=map_point(tuple(map(int,MMSpace.index_to_short('E',idx))),self.inv)
        require(membership(w) and sum(a*a for a in w)==32 and lattice_mod2_encode(w)==y,
                'actual short representative inverse')
        return w

    def real_lift(self,g,deadline=None):
        from mmgroup import Xsp2_Co1
        Xsp2_Co1(g) # fails outside actual G_x0
        B=short_frame()
        images=[]
        for i in range(24):
            if deadline is not None and monotonic()>=deadline:raise TimeoutError('Conway source budget')
            images.append(Matrix(self.short_image(g,tuple(map(int,B[:,i])))))
        R=canonical(orient(B,Matrix.hstack(*images))*B.inv())
        require(R.T*R==Matrix.eye(24),'actual real orthogonality')
        L=basis();T=L.inv()*R*L
        require(all(x.q==1 for x in T) and abs(T.det())==1,'actual lattice automorphism')
        cols=[];linear=0
        for i in range(24):
            x=1<<i
            v=Matrix(lattice_mod2_reopen(x,(0,)*24));w=R*v
            require(all(k.q==1 for k in w),'actual lattice point integrality')
            y,s=self.moved(g,x)
            require(lattice_mod2_encode(tuple(map(int,w)))==y,'real/actual quotient commuting square')
            cols.append(y);linear|=s<<i
        require(len(span(cols))==24,'actual quotient rank')
        for x in (0,1,4096,0xffffff,0xabcdef,0x123456):
            for s in (0,1):
                y,t=lift(cols,(x,s));t^=(x&linear).bit_count()%2
                require(self.moved(g,x,s)==(y,t),'actual central lift correction')
        return R,dict(quotient_columns=cols,linear_sign_correction=linear,
            real_matrix=[[str(x) for x in row] for row in R.tolist()],
            integral_basis_matrix=[[int(x) for x in row] for row in T.tolist()],
            real_determinant=int(R.det()),quotient_basis_checks=24)


def run(a):
    from mmgroup import MM
    raw=a.alignment.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==a.alignment_sha256,'pinned literal alignment')
    f=Alignment(json.loads(raw));deadline=monotonic()+a.seconds
    # Include the nonmonomial xi generator, not just previous 13.
    g=MM(a.word) if a.word else MM('l',1)
    R,r=f.real_lift(g,deadline)
    S,s=f.real_lift(g**-1,deadline)
    I=Matrix.eye(24);sign=signed_composition(R,S,I)
    T,t=f.real_lift(g*g,deadline)
    square_sign=signed_composition(R,R,T)
    return dict(status='actual_Gx0_real_Leech_lift',word=str(g),
        alignment_sha256=a.alignment_sha256,forward=r,inverse=s,square=t,
        inverse_composition_sign=sign,square_composition_sign=square_sign,
        sign_section_not_group_homomorphism=True,
        generic_Gx0_word_evaluator_written=True,
        full_Co1_enumeration_performed=False,original_neural_equivariance_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--alignment',type=Path,required=True);p.add_argument('--alignment-sha256',required=True)
    p.add_argument('--word');p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();require(0<a.seconds<=90,'bounded source budget')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],r['inverse_composition_sign'],r['square_composition_sign'])

if __name__=='__main__':main()
