#!/usr/bin/env python3
"""BR47: exact physical D/E wall-row Leibniz hierarchy through order eight.

Reuses original BR34 *actual* 30 metric + 10 subsidiary rows and pays
derivatives of the varying physical j(t), q(t), without replacing them
with frozen coefficients. The exact reference rows are bilinear in the
background jet and endpoint values. Source-correct generalized Leibniz:
 d^r B(j,q;U) =
 B(j,q;U^(r))+
 Σ_{k=1}^r binom(r,k)(B(j^(k),q^(k);U^(r-k))
                      -B(0,0;U^(r-k))).
No B(j_k,q_k) is a source estimate or an elliptic boundary inverse;
this is the boundary differentiated operator used by BR4 high-order jets.
The nonlinear moving-graph Fréchet terms remain independent BR19 inputs.

Usage: python scripts/check_hopf369_br47_boundary_hierarchy.py
       --sector metric|gauge --order 0..8 --allocation D|E
"""
import argparse
from math import comb
import sympy as s
from check_hopf369_br_warped_physical_attachment import metric_rows,gauge_rows,dec

def raw(order,sector,allocation):
    t=s.symbols('t',real=True)
    j=s.Rational(-6,5)+sum(s.Rational(k+1,k+7)*t**k for k in range(1,order+1))
    q=s.Matrix([s.Rational(i+1,i+4)+
                sum(s.Rational((i+2)*(k+1),k+i+7)*t**k for k in range(1,order+1))
                for i in range(4)])
    n=15 if sector=='metric' else 5
    # Per-component independent polynomial endpoint jets, with scalar
    # coefficient blocks intentionally distinguished across channels.
    vals=[s.Matrix([sum(s.Rational(((i+2)*(p+4)*(k+1))%23-11,
                                  3+i+k)*t**k for k in range(order+1))
                     for i in range(n)]) for p in range(4)]
    if sector=='metric':
        fields=[dec(v) for v in vals]
        def rows(U,b,c):
            return metric_rows(*U,c,b,allocation)
        zero_fields=[dec(s.zeros(15,1)) for _ in range(4)]
    else:
        fields=vals
        def rows(U,b,c):
            return gauge_rows(*U,c,b,allocation)
        zero_fields=[s.zeros(5,1) for _ in range(4)]
    def derive_fields(k):
        return [u.diff(t,k) for u in fields]
    def source(U,jk,qk):
        return rows(U,jk,qk)-rows(U,s.S.Zero,s.zeros(4,1))
    expected=rows(derive_fields(order),j,q)
    for k in range(1,order+1):
        expected+=comb(order,k)*source(derive_fields(order-k),
                                        s.diff(j,t,k),q.diff(t,k))
    direct=rows(fields,j,q).diff(t,order)
    diff=(expected-direct).applyfunc(s.expand)
    assert diff==s.zeros(*diff.shape),(sector,order,allocation)
    # The physical mean-force is the final metric row for either
    # allocation; it cannot be dropped in higher-order trace estimates.
    assert direct.rows==(30 if sector=='metric' else 10)
    assert direct[-1]==expected[-1]
    print('PASS BR47 physical',sector,allocation,'order',order,
          'rows',direct.rows,'source-background terms',order)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--sector',choices=['metric','gauge'],required=True)
    p.add_argument('--order',type=int,required=True)
    p.add_argument('--allocation',choices=['D','E'],required=True)
    a=p.parse_args()
    if not 0<=a.order<=8:raise ValueError('BR4 hierarchy verified only up to order eight')
    raw(a.order,a.sector,a.allocation)
if __name__=='__main__':main()
