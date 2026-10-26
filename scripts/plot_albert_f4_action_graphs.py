#!/usr/bin/env python3
"""Plot the exact standard F4 root/action surfaces recognized by the Albert derivation tranche.

The branch's exact Q(i) producer identifies the 48 nonzero one-dimensional root
spaces with the standard F4 roots 24 + 8 + 8 + 8 and verifies all 1128 unordered
root-pair brackets: 408 root-sum nonzero, 24 opposite-root Cartan, 696 zero.
This renderer uses only that recognized root datum; it does not re-run the large
Albert derivation matrices.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, product
import argparse, json
import matplotlib.pyplot as plt


def dot(x,y):return sum(a*b for a,b in zip(x,y))
def reflect(v,r):
    c=2*dot(v,r)/dot(r,r);return tuple(x-c*a for x,a in zip(v,r))
def row_major(states,cols):return {s:(i%cols,-(i//cols)) for i,s in enumerate(states)}
def roots_f4():
    roots=set()
    for i,j in combinations(range(4),2):
        for si,sj in product((-1,1),repeat=2):
            v=[F(0)]*4;v[i]=F(si);v[j]=F(sj);roots.add(tuple(v))
    for i in range(4):
        for s in (-1,1):
            v=[F(0)]*4;v[i]=F(s);roots.add(tuple(v))
    for signs in product((-1,1),repeat=4):roots.add(tuple(F(s,2) for s in signs))
    return sorted(roots)
SIMPLE=[(F(0),F(1),F(-1),F(0)),(F(0),F(0),F(1),F(-1)),(F(0),F(0),F(0),F(1)),(F(1,2),F(-1,2),F(-1,2),F(-1,2))]
def render_actions(states,actions,cols,path,title):
    pos=row_major(states,cols);fig,ax=plt.subplots(figsize=(9,9))
    for action in actions:
        for s in states:
            t=action(s);x0,y0=pos[s];x1,y1=pos[t]
            ax.annotate('',xy=(x1,y1),xytext=(x0,y0),arrowprops={'arrowstyle':'->','lw':.25,'alpha':.18})
    ax.scatter([pos[s][0] for s in states],[pos[s][1] for s in states],s=18,zorder=3);ax.set_aspect('equal',adjustable='box');ax.axis('off');ax.set_title(title);fig.savefig(path,dpi=220,bbox_inches='tight');plt.close(fig)
def render_edges(states,edges,cols,path,title):
    pos=row_major(states,cols);fig,ax=plt.subplots(figsize=(9,9))
    for a,b in edges:
        x0,y0=pos[a];x1,y1=pos[b];ax.plot([x0,x1],[y0,y1],linewidth=.35,alpha=.10)
    ax.scatter([pos[s][0] for s in states],[pos[s][1] for s in states],s=18,zorder=3);ax.set_aspect('equal',adjustable='box');ax.axis('off');ax.set_title(title);fig.savefig(path,dpi=220,bbox_inches='tight');plt.close(fig)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--outdir',default='outputs/albert_f4_action_graphs');args=ap.parse_args();out=Path(args.outdir);out.mkdir(parents=True,exist_ok=True)
    roots=roots_f4();rootset=set(roots);assert len(roots)==48
    actions=[lambda w,r=r:reflect(w,r) for r in SIMPLE];assert all(a(w) in rootset for a in actions for w in roots)
    render_actions(roots,actions,7,out/'albert_f4_four_simple_reflections.png','Albert F4: 48 roots, four simple reflections')
    sums=[];opposites=[]
    for i,a in enumerate(roots):
        for b in roots[i+1:]:
            s=tuple(x+y for x,y in zip(a,b))
            if s in rootset:sums.append((a,b))
            elif all(x+y==0 for x,y in zip(a,b)):opposites.append((a,b))
    assert len(sums)==408 and len(opposites)==24 and 1128-len(sums)-len(opposites)==696
    render_edges(roots,sums+opposites,7,out/'albert_f4_root_bracket_relation.png','Albert F4 root grading: 408 root-sum + 24 opposite-Cartan pairs')
    meta={'roots':48,'weyl_generators':4,'directed_generator_edges':192,'root_sum_nonzero_pairs':408,'opposite_cartan_pairs':24,'forbidden_sum_zero_pairs':696}
    (out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))
if __name__=='__main__':main()
