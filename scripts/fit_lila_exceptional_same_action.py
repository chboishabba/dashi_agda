#!/usr/bin/env python3
"""Fit held-out LILA/semantic interventions to existing finite exceptional actions.

Input JSON rows:
  {"intervention":"name", "split":"train|heldout",
   "before": <root-index or probability-vector>,
   "after":  <root-index or probability-vector>}
Optional composition declarations:
  {"left":"A", "right":"B", "combined":"A_then_B"}

Families:
  e6-27  : exact 27-weight Weyl permutation action, full W(E6) enumeration.
  e8-240 : standard E8 roots with eight simple reflections, bounded word search.

The script separates action fitting from decoder/model claims. It produces an
empirical SAME-ACTION receipt candidate only when held-out pairs and declared
composition pass; it never turns a fit into mechanism or semantic authority.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def dot(x,y): return sum(a*b for a,b in zip(x,y))
def reflect(v,r):
    c=2*dot(v,r)/dot(r,r)
    return tuple(x-c*a for x,a in zip(v,r))
def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))

def e8_roots():
    roots=[]
    for i in range(8):
        for j in range(i+1,8):
            for si,sj in product((-2,2),repeat=2):
                x=[0]*8;x[i]=si;x[j]=sj;roots.append(tuple(F(v) for v in x))
    for signs in product((-1,1),repeat=8):
        if sum(v<0 for v in signs)%2==0: roots.append(tuple(F(v) for v in signs))
    return roots
E8_SIMPLE=((1,-1,-1,-1,-1,-1,-1,1),(2,2,0,0,0,0,0,0),(-2,2,0,0,0,0,0,0),(0,-2,2,0,0,0,0,0),(0,0,-2,2,0,0,0,0),(0,0,0,-2,2,0,0,0),(0,0,0,0,-2,2,0,0),(0,0,0,0,0,-2,2,0))

def rank(vs):
    rows=[list(v) for v in vs]
    if not rows:return 0
    m,n=len(rows),len(rows[0]);r=c=0
    while r<m and c<n:
        p=next((i for i in range(r,m) if rows[i][c]),None)
        if p is None:c+=1;continue
        rows[r],rows[p]=rows[p],rows[r]
        q=rows[r][c];rows[r]=[x/q for x in rows[r]]
        for i in range(m):
            if i!=r and rows[i][c]:
                q=rows[i][c];rows[i]=[x-q*y for x,y in zip(rows[i],rows[r])]
        r+=1;c+=1
    return r

def e6_weight_data():
    roots=e8_roots()
    av=lambda r:sum(r[5:])/3
    e6=[r for r in roots if r[5:] in ((F(-1),)*3,(F(0),)*3,(F(1),)*3)]
    a2=[r for r in roots if sorted(r[5:])==[F(-2),F(0),F(2)]]
    mixed=[r for r in roots if r not in e6 and r not in a2]
    def a2c(r):
        a=av(r);return tuple(v-a for v in r[5:])
    fibres=defaultdict(list)
    for r in mixed:fibres[a2c(r)].append(r)
    fibre=fibres[sorted(fibres)[0]]
    def proj(r):
        a=av(r);return tuple(r[:5])+(a,a,a)
    weights=sorted({proj(r) for r in fibre})
    simple=[]
    for r in e6:
        if rank(simple+[r])>len(simple):simple.append(r)
        if len(simple)==6:break
    idx={w:i for i,w in enumerate(weights)}
    gens=[tuple(idx[reflect(w,r)] for w in weights) for r in simple]
    return weights,gens

def e8_data():
    roots=sorted(tuple(F(x) for x in r) for r in e8_roots());idx={r:i for i,r in enumerate(roots)}
    gens=[tuple(idx[reflect(w,tuple(F(x) for x in r))] for w in roots) for r in E8_SIMPLE]
    return roots,gens

def enumerate_group(gens,max_depth=None):
    I=tuple(range(len(gens[0])));seen={I:()};q=deque([I])
    while q:
        g=q.popleft();word=seen[g]
        if max_depth is not None and len(word)>=max_depth:continue
        for j,s in enumerate(gens):
            h=compose(s,g)
            if h not in seen:seen[h]=word+(j,);q.append(h)
    return seen

def permute_prob(p,perm):
    out=[0.0]*len(p)
    for i,x in enumerate(p):out[perm[i]]+=float(x)
    return out

def row_loss(row,perm):
    b=row['before'];a=row['after']
    if isinstance(b,int):return 0.0 if perm[b]==a else 1.0
    pred=permute_prob(b,perm)
    return sum((x-float(y))**2 for x,y in zip(pred,a))/len(pred)

def fit_one(rows,candidates):
    best=None
    for perm,word in candidates.items():
        loss=sum(row_loss(r,perm) for r in rows)/max(1,len(rows));key=(loss,len(word),word)
        if best is None or key<best[0]:best=(key,perm,word)
    return best[1],best[2]

def evaluate(rows,perm):
    if not rows:return {'count':0,'loss':None,'exact_accuracy':None}
    loss=sum(row_loss(r,perm) for r in rows)/len(rows);exact=None
    if all(isinstance(r['before'],int) for r in rows):exact=sum(perm[r['before']]==r['after'] for r in rows)/len(rows)
    return {'count':len(rows),'loss':loss,'exact_accuracy':exact}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--family',choices=['e6-27','e8-240'],required=True);ap.add_argument('--input');ap.add_argument('--max-depth',type=int,default=4);ap.add_argument('--output',default='lila_same_action_fit.json');ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    states,gens=e6_weight_data() if args.family=='e6-27' else e8_data()
    candidates=enumerate_group(gens,None if args.family=='e6-27' else args.max_depth)
    if args.family=='e6-27':assert len(candidates)==51840
    if args.self_test:
        A,B=gens[:2];AB=compose(B,A);rows=[]
        for label,p,split in [('A',A,'train'),('A',A,'heldout'),('B',B,'train'),('B',B,'heldout'),('AB',AB,'train'),('AB',AB,'heldout')]:
            inds=range(0,len(states),2) if split=='train' else range(1,len(states),2)
            rows.extend({'intervention':label,'split':split,'before':i,'after':p[i]} for i in inds)
        data={'rows':rows,'compositions':[{'left':'A','right':'B','combined':'AB'}]}
    else:data=json.loads(Path(args.input).read_text())
    grouped=defaultdict(lambda:{'train':[],'heldout':[]})
    for r in data['rows']:grouped[r['intervention']][r.get('split','train')].append(r)
    fits={};perms={}
    for label,parts in grouped.items():
        perm,word=fit_one(parts['train'],candidates);perms[label]=perm
        fits[label]={'word_generator_indices':[i+1 for i in word],'word_length':len(word),'train':evaluate(parts['train'],perm),'heldout':evaluate(parts['heldout'],perm)}
    comps=[]
    for c in data.get('compositions',[]):
        predicted=compose(perms[c['right']],perms[c['left']]);comps.append({**c,'permutation_exact':predicted==perms[c['combined']]})
    paid=all(v['heldout']['count']>0 and (v['heldout']['exact_accuracy']==1.0 if v['heldout']['exact_accuracy'] is not None else v['heldout']['loss']==0.0) for v in fits.values()) and all(c['permutation_exact'] for c in comps)
    result={'family':args.family,'state_count':len(states),'candidate_count':len(candidates),'bounded_search_depth':None if args.family=='e6-27' else args.max_depth,'fits':fits,'composition_checks':comps,'same_action_empirically_paid':paid,'mechanism_identification_paid':False}
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
