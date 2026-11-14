#!/usr/bin/env python3
"""Exact rational sparse polynomial Lie-derivative compiler for original
R853: r(u)=6*(12*C(u)-P(u)+D(u)), u'=F(u), nu=delta=1.
The CLI source JSON is UNTRUSTED until original R71 chart equality,
trajectory and same-object R853 C/P/D are formally proved.
This is algebraic box-bound verification, NOT a physical solution.
"""
from collections import defaultdict
from fractions import Fraction as Q
import argparse,json,math

def clean(p):return {a:c for a,c in p.items() if c}
def add(a,b):
    c=defaultdict(Q,a)
    for k,v in b.items():c[k]+=v
    return clean(c)
def scale(a,b):return clean({k:b*v for k,v in a.items()})
def mul(a,b):
    c=defaultdict(Q)
    for x,ax in a.items():
        for y,by in b.items():c[tuple(i+j for i,j in zip(x,y))]+=ax*by
    return clean(c)
def deriv(a,i):
    b=defaultdict(Q)
    for mon,c in a.items():
        if mon[i]:
            exp=list(mon);exp[i]-=1
            b[tuple(exp)]+=c*mon[i]
    return clean(b)
def ev(a,x):
    return sum((c*math.prod((xx**i for xx,i in zip(x,mon)))
                for mon,c in a.items()),Q())
def box_bound(a,R):
    return sum((abs(c)*R**sum(k) for k,c in a.items()),Q())
def parse(entries,n):
    out={}
    for item in entries:
        k=tuple(item['powers'])
        assert len(k)==n and all(isinstance(i,int) and i>=0 for i in k)
        out[k]=out.get(k,Q())+Q(item['coefficient'])
    return clean(out)
def report(spec):
    names=spec['variables'];n=len(names)
    assert 0<n<=128 and len(set(names))==n
    F=[parse(p,n) for p in spec['F']]; assert len(F)==n
    C=parse(spec['C'],n);P=parse(spec['P'],n);D=parse(spec['D'],n)
    assert all(max((sum(k) for k in f),default=0)<=2 for f in F)
    r=scale(add(add(scale(C,12),scale(P,-1)),D),6)
    lie={}
    for i in range(n):lie=add(lie,mul(deriv(r,i),F[i]))
    R=Q(spec['radius']);assert R>=0
    x0=tuple(Q(v) for v in spec['initial_state'])
    assert len(x0)==n and all(abs(v)<=R for v in x0)
    rate0=ev(r,x0)
    d0=sum((ev(deriv(r,i),x0)*ev(F[i],x0) for i in range(n)),Q())
    assert d0==ev(lie,x0)
    L=Q(391309593930357307785216)
    bound=box_bound(lie,R)
    return {'schema':'ns-r853-sparse-polynomial-lie-v1','result':'PASS',
      'variables':n,'R853_initial_rate':str(rate0),
      'source_R829_initial_rate_exact':rate0==Q(-28273644,125),
      'initial_lie_rate':str(d0),'box_lie_derivative_bound':str(bound),
      'within_R854_claimed_L':bound<=L,
      'within_R855_relaxed_integrated_L':bound<=20000000*L,
      'source_chart_verified':False,'physical_real_solution':False,
      'true_R853_along_solution':False,'integral_closed':False,
      'kernel_receipt':False}
def selftest():
    spec={'variables':['u','v'],'radius':'2','initial_state':['0','0'],
      'C':[{'powers':[0,0],'coefficient':'-557627/125'},
           {'powers':[1,0],'coefficient':'1/3'}],
      'P':[{'powers':[0,1],'coefficient':'1/4'}],
      'D':[{'powers':[0,0],'coefficient':'15834'},
           {'powers':[0,2],'coefficient':'1/7'}],
      'F':[[{'powers':[1,0],'coefficient':'-1'},
            {'powers':[0,1],'coefficient':'1/5'}],
           [{'powers':[1,1],'coefficient':'1/2'},
            {'powers':[0,1],'coefficient':'-2'}]]}
    a=report(spec)
    assert a['source_R829_initial_rate_exact'] and a['initial_lie_rate']=='0'
    spec['initial_state']=['1','0']
    b=report(spec);assert b['initial_lie_rate']!='0'
    return {'result':'PASS','synthetic_exact_cases':2,'report':a,
      'original_physical_source_verified':False,'kernel_receipt':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--certificate');v=p.parse_args()
    print(json.dumps(report(json.load(open(v.certificate))) if v.certificate
      else selftest(),indent=2))
