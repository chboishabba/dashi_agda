"""Actual Y443 source node images via the published Y555 Bimonster map.

Ivanov (1999), DOI 10.1006/jabr.1999.7882; Norton (2002);
Seysen mmgroup.bimm, https://mmgroup.readthedocs.io/en/stable/api.html
JMD literal u/v words from CFSGCorollary/Sporadic/Monster/Y443.lean.
DASHI weld: central twist, actual quotient evaluations, exact word transport.
The published identification Q80 = Monster and simplicity are mathematical
inputs, not derived by computing 80 relators. No selected FLM VOA assumed.
"""
import argparse
from itertools import combinations
from functools import reduce
from pathlib import Path
import json
from time import monotonic
from scripts.check_y443_vnatural_pair_bridge import NODES, EDGES, SPIDER, CENTRAL

SOURCE='https://mmgroup.readthedocs.io/en/stable/api.html'
JMD='https://github.com/AxiomMath/CFSGCorollary/blob/main/CFSGCorollary/Sporadic/Monster/Y443.lean'
U=('d3','c3','b3','a','b1','c1','d1','e1')
BETA=('b2','c2','d2','e2')
V=U+('e1',)+BETA


def require(ok,msg):
    if not ok:raise ValueError(msg)


def relators():
    return ([(n,n) for n in NODES]+
            [tuple(p)*(3 if frozenset(p) in EDGES else 2) for p in combinations(NODES,2)]+
            [tuple(SPIDER)*10,tuple(CENTRAL)*9])


def evaluate(word,nodes,one):
    return reduce(lambda a,n:a*nodes[n],word,one)


def recover_pair(nodes,one):
    u=evaluate(U,nodes,one);v=evaluate(V,nodes,one)
    w=u**-1*v;beta=evaluate(BETA,nodes,one)
    require(w==nodes['e1']*beta and w**5==nodes['e1'] and w**6==beta,'JMD source powers')
    recovered={'e1':w**5};words={'e1':[-1,2]*5}
    # Coxeter path product s0...sn sends s_i to s_(i+1)
    # by left conjugation; recover backwards from final node.
    def path(path,g,gw,known,forward):
        for i,j in zip(path,path[1:]):
            require(g*nodes[i]*g**-1==nodes[j],'original Coxeter path shift')
        if forward:
            for i,j in zip(path,path[1:]):
                recovered[j]=g*recovered[i]*g**-1
                words[j]=gw+words[i]+[-x for x in reversed(gw)]
        else:
            for i,j in zip(reversed(path[1:]),reversed(path[:-1])):
                recovered[j]=g**-1*recovered[i]*g
                words[j]=[-x for x in reversed(gw)]+words[i]+gw
    path(U,u,[1],'e1',False)
    third=('a',)+BETA;g=nodes['a']*beta
    path(third,g,words['a']+[-1,2]*6,'a',True)
    require(set(recovered)==set(NODES),'all twelve source words recovered')
    signed={1:u,-1:u**-1,2:v,-2:v**-1}
    for n in NODES:
        require(recovered[n]==nodes[n]==evaluate(words[n],signed,one),'actual pair recovery '+n)
    return u,v,w,words


def run(seconds):
    from mmgroup import MM
    from mmgroup.bimm import BiMM,P3_BiMM
    from importlib.metadata import version
    require(0<seconds<=90,'bounded scope')
    deadline=monotonic()+seconds
    def budget():
        if monotonic()>=deadline:raise TimeoutError('Y443 source budget')
    one=BiMM(1);mone=MM(1)
    nodes={n:P3_BiMM([n]) for n in NODES}
    c=evaluate(tuple(CENTRAL)*9,nodes,one)
    a,b,e=c.decompose()
    require(e==1 and c!=one and c*c==one,'actual odd central element')
    require(a*b==mone and b*a==mone,'central swap inverse coordinates')
    for n,g in nodes.items():
        budget()
        require(g*g==one and g*c==c*g and g.decompose()[2]==1,'source involution/centrality '+n)
    # Each odd node times the odd central involution is even.
    # Its two projections are conjugate by the first coordinate of c.
    left={};right={}
    for n,g in nodes.items():
        x,y,e=(g*c).decompose()
        require(e==0 and x!=mone and y!=mone,'actual nontrivial quotient node '+n)
        require(y==a**-1*x*a,'central factor-conjugation square '+n)
        left[n]=x;right[n]=y
    R=relators()
    require(len(R)==80 and sum(map(len,R))==463,'original presentation inventory')
    checks=[]
    for i,word in enumerate(R):
        budget()
        raw=evaluate(word,nodes,one)
        require(raw==(c if i==79 else one),'original Bimonster source relator '+str(i))
        require(evaluate(word,left,mone)==mone and evaluate(word,right,mone)==mone,
                'actual quotient relator '+str(i))
        checks.append(i)
    u,v,w,words=recover_pair(left,mone)
    ur,vr,wr,wordsr=recover_pair(right,mone)
    require(words==wordsr and ur==a**-1*u*a and vr==a**-1*v*a,'actual two-factor pair square')
    return dict(status='actual_Y443_Monster_quotient_source',
        basis='Conway-Seysen-MMV-external-196884',source_ref=SOURCE,
        jmd_source_ref=JMD,mmgroup_version=version('mmgroup'),
        original_node_words={n:str(left[n]) for n in NODES},
        second_factor_node_words={n:str(right[n]) for n in NODES},
        central_swap_first_word=str(a),original_relator_checks=checks,
        original_relators_verified=80,original_relator_letters=463,
        words={'u':str(u),'v':str(v)},second_factor_pair={'u':str(ur),'v':str(vr)},
        w_word=str(w),node_words_in_jmd_pair=words,
        node_recovery_count=12,all_word_factor_conjugation_from_generators=True,
        published_ivanov_simple_quotient_required=True,
        nonidentity_node_witness='a',selected_flm_voa_identified=False,
        independent_original_selected_voa_operator_agreement=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=run(a.seconds);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in r.items() if k not in ('original_node_words','second_factor_node_words','node_words_in_jmd_pair')},indent=2))


if __name__=='__main__':main()
