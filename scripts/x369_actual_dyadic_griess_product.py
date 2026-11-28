"""Actual dyadic Griess multiplication by constructive signed-axis expansion.

Conway 1985 Appendix 6; Seysen mmgroup guide, "The Griess algebra
product of a vector and an axis", and C interface mm_op_mul_std_axis.
The C standard-axis operator has eigenvalues 0,1,8,32 and integer
row L1 bound <=64 (largest displayed row is 48). Divide by two for
the package norm-8 axis convention (eigenvalues 0,1/2,4,16).
CRT uniqueness is applied to individual standard-axis operations,
never a whole conjugated word. Existing dyadic group action handles
the two transports. No new VOA or FLM basis is presumed.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from time import monotonic
import argparse
import hashlib
import json
import numpy as np
from scripts.x369_monster_dyadic_source_action import (
    DIM,MODULI,DIGIT_BASE,Dyadic,action,centered_crt,require,unit)
from scripts.x369_actual_griess_axis_generation import (
    AxisTerm,basis_terms,exact_axis,exact_sum,plus,scale)

ROW_BOUND=64


def add(v,w):
    p=max(v.power,w.power)
    return Dyadic(v.numerator*(1<<(p-v.power))+w.numerator*(1<<(p-w.power)),p)


def times(c,v):
    c=F(c);d=c.denominator
    require(d&(d-1)==0,'non-dyadic coefficient')
    return Dyadic(v.numerator*c.numerator,v.power+d.bit_length()-1)


def zero():return Dyadic(np.zeros(DIM,dtype=object))


def check_budget(deadline):
    if deadline is not None and monotonic()>=deadline:raise TimeoutError('Griess product budget')


def standard_scaled_residue(p,numerators):
    from mmgroup import MMV
    from mmgroup.mm_op import mm_op_mul_std_axis
    v=MMV(p)('V',np.asarray(numerators%p,dtype=np.uint8))
    ret=mm_op_mul_std_axis(p,v.data)
    require(ret>=0,'actual standard-axis operator failed')
    return np.asarray(v['E'],dtype=np.int64)%p


def standard_product(v,deadline=None):
    # Recover the integral C operator, then apply its exact factor 1/2.
    a=v.numerator;out=np.zeros(DIM,dtype=object)
    sign=np.where(a<0,-1,1);mag=np.abs(a);place=1
    while np.any(mag):
        check_budget(deadline)
        digits=(mag%DIGIT_BASE)*sign;mag=mag//DIGIT_BASE
        bound=int(np.max(np.abs(digits)))*ROW_BOUND
        residues=[standard_scaled_residue(p,digits) for p in MODULI]
        out+=centered_crt(residues,bound).astype(object)*place
        place*=DIGIT_BASE
    return Dyadic(out,v.power+1)


@lru_cache(maxsize=128)
def axis_word(q,triality):
    from mmgroup import MM,XLeech2
    from mmgroup.axes import Axis
    invol=MM(XLeech2(q));a=Axis('i',invol)
    require(a.g_axis==invol,'actual 2A source axis')
    g=a.g
    if triality:g=g*MM('t',triality)
    return g


def term_axis(t,deadline=None):
    from mmgroup import MM
    a=exact_axis(t.q)
    return action(a,MM('t',t.triality),deadline) if t.triality else a


def standard_axis():
    from mmgroup import MM,XLeech2
    return exact_axis(int(XLeech2(MM('q','v+')).ord))


def axis_product(t,v,deadline=None):
    check_budget(deadline)
    g=axis_word(t.q,t.triality)
    a=term_axis(t,deadline)
    require(action(standard_axis(),g,deadline).same(a),'actual axis conjugation square')
    out=action(standard_product(action(v,g**-1,deadline),deadline),g,deadline)
    return out


def expansion(v,deadline=None):
    terms=[]
    for i in np.flatnonzero(v.numerator):
        check_budget(deadline)
        terms.append(scale(F(v.numerator[i],1<<v.power),basis_terms(int(i))))
    return plus(*terms)


def product_from_terms(terms,v,deadline=None):
    out=zero()
    for t in terms:
        check_budget(deadline)
        out=add(out,times(t.coefficient,axis_product(t,v,deadline)))
    return out


def product(v,w,deadline=None):
    # A finite general evaluator; dense inputs may require many chunks.
    # Verify exact source expansion before using it. No associative law
    # is imposed on the nonassociative Griess product.
    terms=expansion(v,deadline)
    require(exact_sum(terms,deadline).same(v),'axis expansion does not reopen input')
    return product_from_terms(terms,w,deadline)


def modular_product(t,v,p):
    from mmgroup import MMV
    from mmgroup.axes import Axis,Griess
    a=Axis(axis_word(t.q,t.triality))
    return Griess(a,MMV(p)('V',v.residue(p)),p=p,n=8)


def run(a):
    from mmgroup import MM,XLeech2
    from importlib.metadata import version
    deadline=monotonic()+a.seconds
    std=standard_axis()
    require(standard_product(std,deadline).same(times(16,std)),'norm-8 axis product normalization')
    # Ising coordinate e=v+/8 has e*e=2e in this product convention.
    e=times(F(1,8),std)
    require(times(F(1,8),standard_product(e,deadline)).same(times(2,e)),
            'Ising multiplication scaling')
    specs=((300,300),(300,576),(852,24),(98580,147732))
    rows=[]
    for i,j in specs:
        try:
            check_budget(deadline)
            v,w=unit(i),unit(j)
            x=product(v,w,deadline)
            y=product(w,v,deadline)
            require(x.same(y),'actual Griess commutativity')
            for p in (7,31):
                from mmgroup import MMV
                total=MMV(p)(0)
                for t in expansion(v,deadline):
                    c=t.coefficient.numerator*pow(t.coefficient.denominator,-1,p)%p
                    total=total+c*modular_product(t,w,p)
                require(np.array_equal(np.asarray(total['E'],dtype=np.uint8)%p,x.residue(p)),
                        'independent public product path')
            rows.append(dict(left=i,right=j,product_sha256=x.digest(),nonzero=len(x.sparse()),
                commutative=True,public_modular_product_agrees=True))
        except TimeoutError:break
    cov=[]
    if a.source and len(rows)==len(specs):
        raw=a.source.read_bytes()
        require(hashlib.sha256(raw).hexdigest()==a.source_sha256,'pinned actual Y443 source')
        r=json.loads(raw)
        require(r['status']=='actual_Y443_Monster_quotient_source' and r['node_recovery_count']==12,
                'actual Y443 source scope')
        t=AxisTerm(F(1),int(XLeech2(MM('q','v+')).ord))
        v=unit(300)
        for name in ('u','v'):
            try:
                check_budget(deadline)
                g=MM(r['words'][name]);ax=axis_word(t.q,0)*g
                lhs=action(axis_product(t,v,deadline),g,deadline)
                # Product by translated axis, with no need to expand a
                # potentially dense transported vector into basis axes.
                vg=action(v,g,deadline)
                rhs=action(standard_product(action(vg,ax**-1,deadline),deadline),ax,deadline)
                require(lhs.same(rhs),'actual JMD product covariance')
                cov.append(dict(generator=name,product_sha256=lhs.digest(),covariance=True))
            except TimeoutError:break
    complete=len(rows)==len(specs) and (not a.source or len(cov)==2)
    return dict(status='actual_dyadic_griess_product_audit' if complete else 'bounded_incomplete',
        mmgroup_version=version('mmgroup'),standard_axis_eigenvalue=16,ising_product_scaling='axis/8',
        standard_integer_row_bound=ROW_BOUND,rows=rows,requested_pairs=len(specs),
        jmd_covariance=cov,source_sha256=a.source_sha256,
        general_finite_bilinear_evaluator_written=True,
        selected_FLM_invariant_form_and_VOA_identified=False,
        all_basis_products_executed=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=90);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--source',type=Path);p.add_argument('--source-sha256')
    a=p.parse_args()
    require(0<a.seconds<=90 and bool(a.source)==bool(a.source_sha256),'bounded source scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],len(r['rows']),len(r['jmd_covariance']))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
