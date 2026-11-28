"""Full finite E-orbit quotient action for one actual normalizer coset.

The source GAP centralizer is a separate producer. Positive conjugacy
returns an actual MM conjugator; negative results are relative to the
computed full quotient centralizer and the declared kernel E, not a
published character-table class label. No enumeration of 3^13*|Suz|.
"""
import argparse
from collections import deque
from itertools import product
from pathlib import Path
from time import monotonic
import json
import numpy as np
from scripts.x369_3b_E_coset_normal_form import geometry,solve,normal_form,orbit_count
from scripts.x369_actual_3b_atlas_quotient_alignment import (
    J,source_action,log_coord,group_coord,recover_coset,evaluate,require)
from scripts.x369_3b_nonzero_weyl_trace import make_word
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_3b_cyclotomic_projector import digest


def bch(a,b):
    out=(a+b)%3
    out[...,12]=(out[...,12]+2*np.sum((a[...,:12]@J)*b[...,:12],axis=-1))%3
    return out


class Chart:
    def __init__(self,L):
        self.L=np.asarray(L,dtype=np.int64)%3
        S,s,ell,D,basis,p,K=geometry(self.L)
        self.s=s;self.ell=ell;self.K=np.asarray(K,dtype=np.int64).reshape(-1,12)
        self.free=[i for i in range(12) if i not in p]
        P=np.eye(12,dtype=np.int64)
        for row,j in zip(basis,p):P=(P-P[:,j,None]*row)%3
        self.P=P
        V=[solve(D,(P[i]-np.eye(12,dtype=np.int64)[i])%3) for i in range(12)]
        require(all(x is not None for x in V),'quotient chart section')
        self.V=np.stack(V)
        self.powers=3**np.arange(len(self.free)-1,-1,-1,dtype=np.int64)
        self.count=orbit_count(self.L)['E_orbits']

    def split(self,d):
        return (self.s==1)&np.all((d@J.T-self.ell)@self.K.T%3==0,axis=-1)

    def canonical(self,e):
        e=np.asarray(e,dtype=np.int64)%3
        require(e.ndim==2 and e.shape[1]==13,'source log batch')
        x=np.column_stack((e[:,:12]@self.V%3,np.zeros(len(e),dtype=np.int64)))
        u=x@self.L.T%3
        q=bch(bch(x,e),-u)
        require(np.array_equal(q[:,:12],e[:,:12]@self.P%3),'batched quotient reopening')
        q[:,12]*=self.split(q[:,:12])
        return q

    def labels(self,q):
        return 3*(q[:,self.free]@self.powers)+q[:,12]

    def inventory(self):
        n=3**len(self.free)
        d=np.zeros((n,12),dtype=np.int64)
        if self.free:d[:,self.free]=(np.arange(n)[:,None]//self.powers)%3
        split=self.split(d)
        q=np.column_stack((d,np.zeros(n,dtype=np.int64)))
        more=q[split].copy();more[:,12]=1
        last=more.copy();last[:,12]=2
        q=np.concatenate((q,more,last));labels=self.labels(q);order=np.argsort(labels)
        require(len(q)==self.count and len(np.unique(labels))==len(q),'complete canonical E inventory')
        return q[order],labels[order]

    def permutation(self,q,labels,L,offset):
        moved=bch(q@L.T%3,offset)
        target=self.labels(self.canonical(moved))
        index=np.searchsorted(labels,target)
        require(np.all(index<len(labels)) and np.array_equal(labels[index],target),'closed E orbit transport')
        require(len(np.unique(index))==len(index),'centralizer action must be bijective')
        return index.astype(np.int32)


def path_between(perms,start,end,deadline):
    n=len(perms[0]) if perms else max(start,end)+1
    parent=np.full(n,-1,dtype=np.int32);letter=np.full(n,-1,dtype=np.int32)
    parent[start]=start;queue=deque([start]);seen=1
    while queue:
        if monotonic()>=deadline:return None,seen,False
        x=queue.popleft()
        if x==end:
            path=[]
            while x!=start:path.append(int(letter[x]));x=int(parent[x])
            return path[::-1],seen,True
        for i,p in enumerate(perms):
            y=int(p[x])
            if parent[y]<0:
                parent[y]=x;letter[y]=i;seen+=1;queue.append(y)
    return None,seen,True


def partition(perms,n,deadline):
    owner=np.full(n,-1,dtype=np.int32);sizes=[]
    for root in range(n):
        if owner[root]>=0:continue
        queue=deque([root]);owner[root]=root;size=1
        while queue:
            if monotonic()>=deadline:return None
            x=queue.popleft()
            for p in perms:
                y=int(p[x])
                if owner[y]<0:owner[y]=root;queue.append(y);size+=1
                else:require(owner[y]==root,'permutation orbit overlap')
        sizes.append(size)
    require(sum(sizes)==n,'complete finite partition')
    return sorted(sizes)


def run(a):
    from mmgroup import MM
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256);m=local['actual_local_sources']['ternary_manifest']
    check_words(m);z=MM(m['center_word']);A=[MM(x) for x in m['translation_words']]
    B=[MM(x) for x in m['modulation_words']]
    align=read_pinned(a.alignment,a.alignment_sha256);r=read_pinned(a.centralizer,a.centralizer_sha256)
    require(align['status']=='actual_ATLAS_quotient_generator_alignment' and
        align['both_generated_quotient_groups_identified'] is True and align['local_sha256']==a.local_sha256
        and r['status']=='source_GAP_quotient_centralizer' and r['alignment_sha256']==a.alignment_sha256
        and r['local_sha256']==a.local_sha256 and r['full_centralizer_computed_by_GAP'] is True,
        'pinned actual quotient centralizer and BIDI source')
    words={x['name']:MM(x['word']) for x in m['normalizer_lifts']}
    C,D=[evaluate(w,words,MM(1)) for w in align['word_pair']]
    def lift(w):
        require(all(type(i) is int and i in (-2,-1,1,2) for i in w),'source ATLAS word')
        return evaluate([('' if i>0 else '-')+('C' if abs(i)==1 else 'D') for i in w],{'C':C,'D':D},MM(1))
    h=lift(r['representative']);g=lift(r['word']);k=lift(r['left_conjugator'])
    left=MM(a.left_word) if a.left_word else g
    right=MM(a.right_word) if a.right_word else h
    recover_coset(left,g,z,A,B);recover_coset(right,h,z,A,B)
    L=source_action(h,z,A,B);chart=Chart(L);q,labels=chart.inventory()
    e=log_coord(recover_coset(k*left*k**-1,h,z,A,B))
    f=log_coord(recover_coset(right,h,z,A,B))
    start,end=map(int,np.searchsorted(labels,chart.labels(chart.canonical(np.stack((e,f))))))
    lifts=[];perms=[]
    base=dict(local_sha256=a.local_sha256,alignment_sha256=a.alignment_sha256,
        centralizer_sha256=a.centralizer_sha256,canonical_E_orbits=len(q),
        left_word=str(left),right_word=str(right),full_cover_class_identified=False)
    for w in r['centralizer_words']:
        if monotonic()>=deadline:return dict(base,status='bounded_incomplete',generator_count=len(perms))
        u=lift(w);M=source_action(u,z,A,B)
        delta=log_coord(recover_coset(u*h*u**-1,h,z,A,B))
        perms.append(chart.permutation(q,labels,M,delta));lifts.append(u)
    path,n,complete=path_between(perms,start,end,deadline)
    if not complete:return dict(base,status='bounded_incomplete',orbit_vertices_seen=n)
    out=dict(base,status='actual_normalizer_conjugator' if path is not None else 'closed_relative_orbit_separation',
        orbit_vertices_seen=n,centralizer_generators=len(perms),
        independent_full_centralizer_completeness_proof=False)
    if path is not None:
        for i in path:k=lifts[i]*k
        moved=k*left*k**-1
        a0=log_coord(recover_coset(moved,h,z,A,B))
        q0,x,_=normal_form(L,a0);q1,y,_=normal_form(L,f)
        require(np.array_equal(q0,q1),'retained orbit path endpoint')
        k=make_word(group_coord(y),z,A,B)**-1*make_word(group_coord(x),z,A,B)*k
        require(k*left*k**-1==right,'actual literal normalizer conjugacy')
        out.update(literal_conjugator=str(k),actual_MM_conjugacy_verified=True,centralizer_path=path)
    else:
        out.update(actual_MM_conjugacy_verified=False,
            negative_relative_to_GAP_full_centralizer_and_E_kernel=True)
    if a.partition:
        sizes=partition(perms,len(q),deadline)
        out['full_relative_coset_partition_complete']=sizes is not None
        out['relative_class_orbit_sizes']=sizes
    return out


def main():
    p=argparse.ArgumentParser()
    for n in ('local','alignment','centralizer'):
        p.add_argument('--'+n,type=Path,required=True);p.add_argument('--'+n+'-sha256',required=True)
    p.add_argument('--left-word');p.add_argument('--right-word');p.add_argument('--partition',action='store_true')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();require(0<a.seconds<=90,'bounded actual source')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))
    if r['status']=='bounded_incomplete' or (a.partition and not r.get('full_relative_coset_partition_complete')):raise SystemExit(2)

if __name__=='__main__':main()
