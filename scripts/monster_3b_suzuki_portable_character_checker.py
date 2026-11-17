#!/usr/bin/env python3
"""Portable, exact Q(zeta_3) full-class Suzuki Sym^2/dual comparator.

Input: exported group character values [a,b] = a + b*zeta, with
zeta^2+zeta+1=0, and a ZERO-BASED second-power class map.

An exported table is an INPUT, not proof of its authorship or GAP execution.
The consumer independently checks actual row equality and supplies a first
counterexample when rows differ. Source mathematical identity is classical:
chi_Sym2(g)=(chi(g)^2+chi(g^2))/2.

ATTRIBUTION: representation identity from standard character theory (Serre);
Monster table/fusions from Barraclough--Wilson (2007), source owner
https://www.rwb.me.uk/table/index.html ; irreducible Sym²12=78 existence
from Gabriele Nebe (2025), DOI 10.1007/s10801-025-01399-2. This
pure-Python program does not certify that a source export was authentic.
"""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

def raw(x):
    if not isinstance(x,(list,tuple)) or len(x)!=2:
        raise ValueError('need [a,b] in Q(zeta_3)')
    if any(type(v) not in (int,str) for v in x):
        raise ValueError('coefficients must be exact integers or rational strings')
    return tuple(Q(z) for z in x)

def add(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,y):
    a,b=x;c,d=y
    return a*c-b*d,a*d+b*c-b*d

def half(x):return x[0]/2,x[1]/2
def conj(x):return x[0]-x[1],-x[1]
def equals_integer(x,n):return x==(Q(n),Q(0))
def serial(x):return [str(x[0]),str(x[1])]

def check(data):
    if not isinstance(data,dict):raise ValueError('source JSON must be object')
    tbl=data.get('table_id')
    if type(tbl) is not str or not tbl:raise ValueError('table_id required')
    orders=data.get('class_orders')
    power=data.get('power_map_2_zero_based')
    if not isinstance(orders,list) or len(orders)<2 or any(type(v) is not int or v<1 for v in orders):
        raise ValueError('class orders required')
    n=len(orders)
    if orders[0]!=1:raise ValueError('class zero must be identity')
    if not isinstance(power,list) or len(power)!=n or any(type(v) is not int or v not in range(n) for v in power):
        raise ValueError('complete power map required')
    if power[0]!=0:raise ValueError('identity must square to identity')
    from math import gcd
    for k,(order,dest) in enumerate(zip(orders,power)):
        if orders[dest]!=order//gcd(order,2):
            raise ValueError(f'wrong square class order at {k}')
    def get_rows(key,degree):
        rows=data.get(key)
        if not isinstance(rows,list) or not rows:raise ValueError(f'{key} missing')
        ans=[];labels=set()
        for row in rows:
            if not isinstance(row,dict) or not isinstance(row.get('label'),str) or not row['label']:
                raise ValueError(f'{key}: label missing')
            if row['label'] in labels:raise ValueError('duplicate row label')
            labels.add(row['label'])
            if not isinstance(row.get('values'),list) or len(row['values'])!=n:
                raise ValueError(f'{key}: need all {n} class values')
            values=[raw(v) for v in row['values']]
            if not equals_integer(values[0],degree):
                raise ValueError(f'{row["label"]}: wrong degree')
            ans.append((row['label'],values))
        return ans
    rows12=get_rows('degree12',12)
    rows78=get_rows('degree78',78)
    sizes=data.get('class_sizes')
    order=data.get('group_order')
    if tbl=='6.Suz' and (sizes is None or order is None):
        raise ValueError('6.Suz source export must include full class sizes and group order')
    if sizes is not None or order is not None:
        if (not isinstance(sizes,list) or len(sizes)!=n
            or any(type(z) is not int or z<1 for z in sizes)
            or type(order) is not int or order<1
            or sum(sizes)!=order or sizes[0]!=1):
            raise ValueError('class sizes and group order not consistent')
        # Independently test source claims of character irreducibility via
        # exact class-weighted inner products, no floating-point rounding.
        rows=rows12+rows78
        for i,(name_i,chi) in enumerate(rows):
            for j,(name_j,psi) in enumerate(rows):
                scalar=(Q(0),Q(0))
                for k,weight in enumerate(sizes):
                    v=mul(chi[k],conj(psi[k]))
                    scalar=add(scalar,(weight*v[0],weight*v[1]))
                expected=order if i==j else 0
                if scalar!=(Q(expected),Q(0)):
                    raise ValueError('source irreducible character orthogonality fails: '
                                     +name_i+' / '+name_j)
    c2=data.get('central_c2_zero_based')
    c3=data.get('central_c3_zero_based')
    if type(c2) is not int or c2 not in range(n) or orders[c2]!=2:
        raise ValueError('exact central involution class required')
    if type(c3) is not int or c3 not in range(n) or orders[c3]!=3:
        raise ValueError('exact central C3 class required')
    if sizes is not None and (sizes[c2]!=1 or sizes[c3]!=1):
        raise ValueError('the declared central classes must each have size one')
    roots2={(Q(12),Q(0)),(Q(-12),Q(0))}
    if any(r[c2] not in roots2 for _,r in rows12):
        raise ValueError('central C2 not scalar on 12')
    matches=[];first_differences=[]
    for la,a in rows12:
        squares=[half(add(mul(a[k],a[k]),a[power[k]])) for k in range(n)]
        assert equals_integer(squares[0],78)
        for lb,b in rows78:
            for mode,test in (('Sym2',squares),('dualSym2',[conj(v) for v in squares])):
                diff=next((k for k in range(n) if test[k]!=b[k]),None)
                if diff is None:
                    matches.append({'12':la,'78':lb,'mode':mode,
                        'c2_character78':serial(b[c2]),
                        'central_c3_character78':serial(b[c3])})
                else:
                    first_differences.append({'12':la,'78':lb,'mode':mode,
                         'class_index':diff,'predicted':serial(test[diff]),
                         'source_row':serial(b[diff])})
    return {'status':'exact_character_arithmetic_checked',
        'source_table_id_as_provided':tbl,'classes_tested':n,
        'table_provenance_authenticated':False,
        'character_rows12':len(rows12),'character_rows78':len(rows78),
        'full_class_function_matches':matches,
        'first_disagreements':first_differences,
        'no_monster_quotient_or_same_object_claim':True,
        'no_GAP_execution_claim':True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source_json',type=Path)
    p.add_argument('--out',type=Path)
    args=p.parse_args()
    result=check(json.loads(args.source_json.read_text()))
    text=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
