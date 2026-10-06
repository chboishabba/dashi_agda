#!/usr/bin/env python3
from __future__ import annotations

import itertools, json
import numpy as np
from exceptional_e8_centralizer_transport import (
    P, J, WORD_A, WORD_B, e8_data, eval_word, induced, generated_group
)


def canon(v):
    v=tuple(int(x)%P for x in v)
    for a in v:
        if a:
            inv=1 if a==1 else 2
            return tuple((inv*x)%P for x in v)
    raise ValueError


def symp(u,v):
    return sum(u[i]*J[i,j]*v[j] for i in range(4) for j in range(4))%P


def lines40():
    pts=sorted({canon(v) for v in itertools.product(range(P),repeat=4) if any(v)})
    out=set()
    for a,b in itertools.combinations(pts,2):
        if symp(a,b): continue
        line=frozenset(canon(tuple((x*a[i]+y*b[i])%P for i in range(4)))
                       for x,y in itertools.product(range(P),repeat=2) if x or y)
        if len(line)==4: out.add(line)
    return list(out)


def act_line(a,line):
    return frozenset(canon(a@np.array(v,dtype=int)) for v in line)


def compute_receipt():
    _,refs,_=e8_data()
    aa=induced(eval_word(WORD_A,refs)); ab=induced(eval_word(WORD_B,refs))
    group,complete=generated_group((aa,ab),4,mod=P,limit=60000)
    assert complete and len(group)==51840
    lines=lines40(); idx={L:i for i,L in enumerate(lines)}
    identity=tuple(range(40)); perms=set(); kernel=[]
    for a in group.values():
        p=tuple(idx[act_line(a,L)] for L in lines)
        perms.add(p)
        if p==identity: kernel.append(a)
    assert len(lines)==40 and len(perms)==25920 and len(kernel)==2
    plus=np.eye(4,dtype=int)%P; minus=(2*plus)%P
    assert all(any(np.array_equal(k,z) for z in (plus,minus)) for k in kernel)
    return {
      "symplectic_lines":40,
      "sp4_order":len(group),
      "projective_kernel_order":len(kernel),
      "projective_kernel_is_plus_minus_identity":True,
      "effective_line_action_order":len(perms),
      "centralizer_line_action_is_index_two_vs_51840_e6_null_action":True
    }

if __name__=='__main__': print(json.dumps(compute_receipt(),indent=2,sort_keys=True))
