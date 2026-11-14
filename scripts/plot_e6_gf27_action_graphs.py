#!/usr/bin/env python3
"""Fixed-lattice plots for the exact E6-27 and GF(27) Frobenius actions.

No force-directed layout is used. Node positions are deterministic row-major
coordinates so visual texture comes from the action/state ordering.

E6 data reproduces `check_e6_minuscule27_weight_action.py`.
GF(27) uses F3[a]/(a^3+2a+1); unlike x^3+x+2, this cubic has no F3 root.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import defaultdict, Counter
import argparse, csv, json
import matplotlib.pyplot as plt


def row_major(states,cols): return {s:(i%cols,-(i//cols)) for i,s in enumerate(states)}
def render(states,actions,cols,path,title,alpha=.12,node_size=18):
    states=list(states);pos=row_major(states,cols);fig,ax=plt.subplots(figsize=(9,9))
    for action in actions:
        for s in states:
            t=action(s);x0,y0=pos[s];x1,y1=pos[t]
            ax.annotate('',xy=(x1,y1),xytext=(x0,y0),arrowprops={'arrowstyle':'->','lw':.25,'alpha':alpha})
    ax.scatter([pos[s][0] for s in states],[pos[s][1] for s in states],s=node_size,zorder=3)
    ax.set_aspect('equal',adjustable='box');ax.axis('off');ax.set_title(title);fig.savefig(path,dpi=220,bbox_inches='tight');plt.close(fig)
def render_edges(states,edges,cols,path,title,alpha=.15,node_size=18):
    states=list(states);pos=row_major(states,cols);fig,ax=plt.subplots(figsize=(9,9))
    for a,b in edges:
        x0,y0=pos[a];x1,y1=pos[b];ax.plot([x0,x1],[y0,y1],linewidth=.35,alpha=alpha)
    ax.scatter([pos[s][0] for s in states],[pos[s][1] for s in states],s=node_size,zorder=3)
    ax.set_aspect('equal',adjustable='box');ax.axis('off');ax.set_title(title);fig.savefig(path,dpi=220,bbox_inches='tight');plt.close(fig)
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def reflect(v,r):
    c=2*dot(v,r)/dot(r,r);return tuple(x-c*a for x,a in zip(v,r))
def roots_e8():
    out=[]
    for i in range(8):
        for j in range(i+1,8):
            for si,sj in product((-2,2),repeat=2):
                x=[0]*8;x[i]=si;x[j]=sj;out.append(tuple(F(v) for v in x))
    for signs in product((-1,1),repeat=8):
        if sum(v<0 for v in signs)%2==0:out.append(tuple(F(v) for v in signs))
    return out
def rank(vs):
    rows=[list(v) for v in vs]
    if not rows:return 0
    m,n=len(rows),len(rows[0]);r=c=0
    while r<m and c<n:
        p=next((i for i in range(r,m) if rows[i][c]),None)
        if p is None:c+=1;continue
        rows[r],rows[p]=rows[p],rows[r];q=rows[r][c];rows[r]=[x/q for x in rows[r]]
        for i in range(m):
            if i!=r and rows[i][c]:q=rows[i][c];rows[i]=[x-q*y for x,y in zip(rows[i],rows[r])]
        r+=1;c+=1
    return r
def e6_data():
    roots=roots_e8();av=lambda r:sum(r[5:])/3
    e6=[r for r in roots if r[5:] in ((F(-1),)*3,(F(0),)*3,(F(1),)*3)]
    a2=[r for r in roots if sorted(r[5:])==[F(-2),F(0),F(2)]];mixed=[r for r in roots if r not in e6 and r not in a2]
    def key(r):a=av(r);return tuple(v-a for v in r[5:])
    fib=defaultdict(list)
    for r in mixed:fib[key(r)].append(r)
    fibre=fib[sorted(fib)[0]]
    def proj(r):a=av(r);return tuple(r[:5])+(a,a,a)
    weights=sorted({proj(r) for r in fibre});simple=[]
    for r in e6:
        if rank(simple+[r])>len(simple):simple.append(r)
        if len(simple)==6:break
    return weights,e6,simple

def gf_mul(x,y):
    tmp=[0]*5
    for i,a in enumerate(x):
        for j,b in enumerate(y):tmp[i+j]=(tmp[i+j]+a*b)%3
    for k in (4,3):
        c=tmp[k]%3
        if c:tmp[k]=0;tmp[k-2]=(tmp[k-2]+c)%3;tmp[k-3]=(tmp[k-3]+2*c)%3
    return tuple(tmp[:3])
def gf_pow(x,n):
    y=(1,0,0);b=x
    while n:
        if n&1:y=gf_mul(y,b)
        b=gf_mul(b,b);n//=2
    return y
def frob(x):return gf_pow(x,3)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--outdir',default='outputs/exceptional_action_graphs');args=ap.parse_args();out=Path(args.outdir);out.mkdir(parents=True,exist_ok=True)
    weights,e6,simple=e6_data();actions6=[lambda w,r=r:reflect(w,r) for r in simple];actions72=[lambda w,r=r:reflect(w,r) for r in e6]
    render(weights,actions6,6,out/'e6_minuscule27_six_generators.png','E6 minuscule 27: six generating reflections',.22,22)
    render(weights,actions72,6,out/'e6_minuscule27_all72_reflections.png','E6 minuscule 27: all 72 root reflections',.035,22)
    e6set=set(e6);edges=[]
    for i,w in enumerate(weights):
        for z in weights[i+1:]:
            if tuple(a-b for a,b in zip(w,z)) in e6set or tuple(b-a for a,b in zip(w,z)) in e6set:edges.append((w,z))
    assert len(edges)==216
    render_edges(weights,edges,6,out/'e6_minuscule27_root_difference_graph.png','E6 minuscule 27: 16-regular root-difference graph',.18,24)
    gf=list(product(range(3),repeat=3));assert all(gf_pow(x,27)==x for x in gf);orbits=[];seen=set()
    for x in gf:
        if x in seen:continue
        o=[];y=x
        while y not in o:o.append(y);seen.add(y);y=frob(y)
        orbits.append(o)
    assert Counter(map(len,orbits))==Counter({3:8,1:3})
    render(gf,[frob],6,out/'gf27_frobenius_action.png','GF(27) Frobenius x↦x³: 3 fixed + 8 three-cycles',.35,28)
    meta={'e6_minuscule27':{'nodes':27,'six_generator_edges':162,'all72_edges':1944,'root_difference_edges':216,'degree':16,'weyl_order':51840},'gf27':{'presentation':'F3[a]/(a^3+2a+1)','nodes':27,'fixed':3,'three_cycles':8}}
    (out/'e6_gf27_metadata.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))
if __name__=='__main__':main()
