#!/usr/bin/env python3
"""Deterministic lower-bound certificate on the original ATLAS GF3 generators.
Upper bound is the published 2.Suz:2 order, not inferred from relators.
Optional literal cover replay uses the existing native canonical producer.
"""
import argparse, hashlib, json
from pathlib import Path
from math import prod
import numpy as np

N=12
ORDER=1793381990400
POW=3**np.arange(N,dtype=np.int32)
SIZE=3**N
I=np.eye(N,dtype=np.int32)
SOURCES={
 '2Suzd2G1-f3r12aB0.m1':'ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2',
 '2Suzd2G1-f3r12aB0.m2':'433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f',
}
# BFS ordering is fixed: current frontier, generator order, first discovery.
# Each pair is an orbit point encoded in radix3 and a generator index.
CHAIN=(
 (0,465920,((178594,0),(434894,0),(228493,1),(426185,1),(253536,1),(2849,1),(137364,1),(28112,0),(464918,1),(323979,0),(368455,0),(372675,1))),
 (1,106920,((130379,7),(417764,8),(204449,2),(312250,11),(390955,6),(5682,5),(271781,0),(436352,4),(496268,8),(438307,9),(296075,1),(134747,0))),
 (2,36,()),
)

def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def source(root):
    out=[]
    for name,digest in SOURCES.items():
        path=root/'data'/'atlas'/name
        require(sha(path)==digest,'pinned ATLAS source mismatch '+name)
        words=path.read_text().split();raw=''.join(words[4:])
        require(words[:4]==['1','3','12','12'] and len(raw)==144 and set(raw)<=set('012'),'MeatAxe chart')
        out.append(np.array(list(map(int,raw)),dtype=np.int32).reshape(N,N))
    return out

def inv(A):
    X=np.hstack((A,I)).copy()%3
    for i in range(N):
        nz=np.flatnonzero(X[i:,i]);require(len(nz)>0,'singular generator')
        j=i+int(nz[0]);X[[i,j]]=X[[j,i]];X[i]=X[i]*X[i,i]%3
        for j in range(N):
            if j!=i:X[j]=(X[j]-X[j,i]*X[i])%3
    B=X[:,N:];require(np.array_equal(A@B%3,I) and np.array_equal(B@A%3,I),'inverse residual')
    return B

def orbit(gs,b,V):
    parent=np.full(SIZE,-1,dtype=np.int32);edge=parent.copy();parent[b]=b
    front=np.array([b],dtype=np.int32);parts=[front]
    while len(front):
        new=[]
        for i,g in enumerate(gs):
            dst=(V[front]@g.T%3)@POW
            mask=parent[dst]<0;d=dst[mask];f=front[mask]
            parent[d]=f;edge[d]=i;new.append(d)
        front=np.concatenate(new);parts.append(front)
    return np.concatenate(parts),parent,edge

def trans(gs,b,x,parent,edge,V):
    require(0<=x<SIZE and parent[x]>=0,'Schreier point outside orbit')
    start=x;A=I.copy()
    while x!=b:
        A=A@gs[edge[x]]%3;x=int(parent[x])
    require(np.array_equal(A@V[b]%3,V[start]),'transversal endpoint residual')
    return A

def verify(gs,chain=CHAIN):
    V=(np.arange(SIZE,dtype=np.int32)[:,None]//POW)%3
    sizes=[];fixed=[];witnesses=0;levels=[]
    for j,size,choices in chain:
        require(j not in fixed and 0<=j<N,'bad base index')
        for g in gs:
            inv(g)
            require(all(np.array_equal(g[:,k],I[:,k]) for k in fixed),'generator not in previous stabilizer')
        b=int(POW[j]);o,pa,ed=orbit(gs,b,V)
        require(len(o)==size,'orbit size residual')
        new=[]
        for x,i in choices:
            require(0<=i<len(gs) and 0<=x<SIZE and pa[x]>=0,'bad Schreier index')
            y=int((gs[i]@V[x]%3)@POW)
            h=inv(trans(gs,b,y,pa,ed,V))@gs[i]@trans(gs,b,x,pa,ed,V)%3
            require(all(np.array_equal(h[:,k],I[:,k]) for k in fixed+[j]),'Schreier stabilizer residual')
            require(not np.array_equal(h,I) and not any(np.array_equal(h,t) for t in new),'duplicate or trivial witness')
            new.append(h);witnesses+=1
        levels.append({'base_coordinate':j,'orbit_size':size,'input_generators':len(gs),'schreier_generators':len(new)})
        fixed.append(j);sizes.append(size);gs=new
    lower=prod(sizes)
    require(lower==ORDER,'lower bound does not saturate published upper bound')
    return {'status':'ATLAS_GENERATION_LOWER_BOUND_SATURATES_PUBLISHED_ORDER','levels':levels,'schreier_witnesses':witnesses,'order_lower_bound':lower,'published_order_upper_bound':ORDER,'upper_bound_is_external_source_premise':True}

def attach(root,manifest,cover,atlas):
    from monster3b_mmgroup_canonical_cover_words import full
    from monster3b_literal_standard_D_phase import run as phase
    old=json.loads(cover.read_text());new=full(json.loads(manifest.read_text()),root)
    for key in ('canonical_C_word','canonical_D_word','canonical_C','canonical_D','central_cover_relators','original_source_blob_sha'):
        require(old[key]==new[key],'literal source replay mismatch '+key)
    T=np.asarray(new['ATLAS_GF3_intertwiner']['T_rows_F3'],dtype=np.int32);inv(T)
    for g,A in zip(('C','D'),atlas):
        M=np.asarray(new['canonical_'+g]['matrix_F3'],dtype=np.int32)
        require(np.array_equal(A@T%3,T@M%3),'literal quotient generator transport residual')
        require(not any(new['canonical_'+g]['affine_ell_F3']),'literal affine residual')
    p=phase(manifest,cover)
    require(p['checks']['original_R7'] and p['raw_wheel_has_order13'],'literal centre/wheel residual')
    return {'status':'LITERAL_COVER_GENERATION_ATTACHED','manifest_sha256':sha(manifest),'cover_sha256':sha(cover),'quotient_order':ORDER,'cover_order':3*ORDER,'actual_literal_R7_marks_centre':True,'phase':p,'premise':'published N/E order and zero-affine kernel exactly Z(E); original E and normalizer source authority retained','independent_BW_character_authentication':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--manifest',type=Path);p.add_argument('--cover',type=Path);p.add_argument('--out',type=Path);a=p.parse_args()
    if bool(a.manifest)!=bool(a.cover):p.error('provide both original manifest and cover')
    gs=source(a.root);r=verify(gs)
    if a.manifest:r['literal_attachment']=attach(a.root,a.manifest,a.cover,gs)
    if a.out:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
