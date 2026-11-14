#!/usr/bin/env python3
"""Y443 exact source 80-relator and u/v candidate permutation-action verifier.

Accepts external JSON action data. This does NOT infer faithfulness or full
Monster identification, and a trivial action is valid but nonfaithful.
"""
import argparse
import json
from itertools import combinations

N=("a","b1","c1","d1","e1","b2","c2","d2","e2","b3","c3","d3")
E={frozenset(x) for x in (
 ("a","b1"),("b1","c1"),("c1","d1"),("d1","e1"),
 ("a","b2"),("b2","c2"),("c2","d2"),("d2","e2"),
 ("a","b3"),("b3","c3"),("c3","d3"))}
SP=("a","b1","c1","a","b2","c2","a","b3","c3")
CE=("a","b3","c3","d3","b1","c1","b2")
U=("d3","c3","b3","a","b1","c1","d1","e1")
B=("b2","c2","d2","e2")
V=U+("e1",)+B

def relators():
    out=[("square:"+a,(a,a)) for a in N]
    for a,b in combinations(N,2):
        adjacent=frozenset((a,b)) in E
        out.append((("edge" if adjacent else "nonedge")+":"+a+":"+b,
                    (a,b)*(3 if adjacent else 2)))
    return out+[("spider",SP*10),("central",CE*9)]

def load(path):
    with open(path,encoding="utf8") as f:d=json.load(f)
    degree=d["degree"]
    assert isinstance(degree,int) and degree>0
    g=d["generators"]
    assert set(g)==set(N),"all and only the 12 source generators required"
    assert all(len(v)==degree and sorted(v)==list(range(degree))
               for v in g.values()),"not a permutation assignment"
    return degree,{name:tuple(g[name]) for name in N}

def compose(p,q):
    return tuple(p[q[i]] for i in range(len(p)))

def evaluation(word,assignment):
    ans=tuple(range(len(next(iter(assignment.values())))))
    for n in word:ans=compose(ans,assignment[n])
    return ans

def audit(path):
    degree,assignment=load(path)
    identity=tuple(range(degree))
    failing=[name for name,w in relators()
             if evaluation(w,assignment)!=identity]
    return dict(path=path,degree=degree,relators_passed=80-len(failing),
                failing=failing,u=evaluation(U,assignment),
                v=evaluation(V,assignment),
                nontrivial=any(assignment[n]!=identity for n in N))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("action",help="JSON degree + 12 permutation arrays")
    parser.add_argument("--compare",help="second action on the same carrier")
    args=parser.parse_args()
    a=audit(args.action)
    result=dict(A={k:v for k,v in a.items() if k not in ("u","v")},
                source_word_u=list(U),source_word_v=list(V),
                relators_complete_in_A=a["relators_passed"]==80,
                proves_Monster_faithfulness=False)
    if args.compare:
        b=audit(args.compare)
        assert a["degree"]==b["degree"],"not the same carrier"
        result["B"]={k:v for k,v in b.items() if k not in ("u","v")}
        result["same_on_u"]=a["u"]==b["u"]
        result["same_on_v"]=a["v"]==b["v"]
        result["all_group_agreement_gate_passed"]=(
            a["relators_passed"]==b["relators_passed"]==80
            and result["same_on_u"] and result["same_on_v"])
        result["proves_same_original_Monster_group"]=False
    print(json.dumps(result,indent=2))
    if a["failing"] or (
        args.compare and (b["failing"] or not result["all_group_agreement_gate_passed"])
    ):
        raise SystemExit(1)

if __name__=="__main__":
    main()
