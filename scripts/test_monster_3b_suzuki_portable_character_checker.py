#!/usr/bin/env python3
"""Exact finite-class regression for portable full-class Q(zeta3) checker.

Runs with standard-library Python only. All data are genuine characters of
C2 x C3 (or deliberately malformed negative controls), NOT Monster data.
"""
import copy
import itertools
import json

import monster_3b_suzuki_portable_character_checker as m

def run():
    group=list(itertools.product(range(2),range(3)))
    where={x:i for i,x in enumerate(group)}
    orders=[1 if g==(0,0) else 2 if g[0] and not g[1]
            else 3 if not g[0] and g[1] else 6 for g in group]
    power=[where[(0,(2*y)%3)] for t,y in group]
    roots=((1,0),(0,1),(-1,-1))
    a=[[(-12 if t else 12)*roots[y][0],
        (-12 if t else 12)*roots[y][1]] for t,y in group]
    squares=[m.half(m.add(m.mul(m.raw(a[k]),m.raw(a[k])),
                m.raw(a[power[k]]))) for k in range(len(group))]
    b=[[int(t) for t in v] for v in squares]
    dual=[[int(t) for t in m.conj(v)] for v in squares]
    false=copy.deepcopy(b); false[4][0]+=1
    base={'table_id':'SYNTHETIC:C2xC3','class_orders':orders,
        'power_map_2_zero_based':power,
        'central_c2_zero_based':where[(1,0)],
        'central_c3_zero_based':where[(0,1)],
        'degree12':[{'label':'12','values':a}],
        'degree78':[{'label':'78_true','values':b},
                    {'label':'78_dual','values':dual},
                    {'label':'78_false_class','values':false}]}
    result=m.check(base)
    matches={(x['78'],x['mode']) for x in result['full_class_function_matches']}
    assert ('78_true','Sym2') in matches
    assert ('78_dual','dualSym2') in matches
    assert all(x[0]!='78_false_class' for x in matches)
    assert len(result['first_disagreements'])>=1
    cases=[('missing power map',{'power_map_2_zero_based':[]}),
           ('misindexed square map',{'power_map_2_zero_based':[0]*6}),
           ('wrong central C2',{'central_c2_zero_based':where[(0,1)]}),
           ('missing source class',{'class_orders':orders[:-1]}),
           ('invalid character degree',{'degree12':[{'label':'12','values':[[0,0]]+a[1:]}]}),
           ('duplicated labels',{'degree78':[{'label':'x','values':b},
                                          {'label':'x','values':dual}]})]
    cases.append(('fake Suzuki table without source class sizes',
                  {'table_id':'6.Suz'}))
    cases.append(('invalid claimed source group order',
                  {'group_order':7,'class_sizes':[1]*6}))
    for name,patch in cases:
        trial=copy.deepcopy(base);trial.update(patch)
        try:m.check(trial)
        except ValueError:pass
        else:raise AssertionError(f'Invalid candidate accepted: {name}')
    # Independently check scalar-product arithmetic on honest 1D characters.
    c1=[m.raw(roots[y]) for t,y in group]
    c2=[m.raw([(-1 if t else 1)*roots[y][0],
                (-1 if t else 1)*roots[y][1]]) for t,y in group]
    orth=m.raw([0,0]); norm=m.raw([0,0])
    for q,v in zip(c1,c2):
        orth=m.add(orth,m.mul(q,m.conj(v)))
        norm=m.add(norm,m.mul(q,m.conj(q)))
    assert orth==m.raw([0,0]) and norm==m.raw([6,0])
    return {'status':'PASS','group':'C2 x C3','class_count':len(group),
        'matches':list(map(list,sorted(matches))),
        'negative_controls':len(cases),
        'full_class_negative_witnesses':len(result['first_disagreements']),
        'source_authenticity_verified':False,'GAP_executed':False}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
