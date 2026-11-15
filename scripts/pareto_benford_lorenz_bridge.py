"""Conditional Pareto/Benford/Lorenz/Gini bridges.

Classical distribution identities retain historical original authorship.
Source-written mathematical implementation: Johl Brown with ChatGPT,
2026-10-27. No real-world empirical distribution is asserted to be Pareto.
Pareto minimum=1 in the leading-digit formula.
"""
from __future__ import annotations
from fractions import Fraction
from math import expm1,isfinite,log,log1p

def pareto_leading_digit_exact(base:int,digit:int,alpha:int)->Fraction:
    """Pr(leading base-b digit=d), Pareto(minimum=1, positive integer shape)."""
    if not isinstance(base,int) or base<2 or not isinstance(digit,int) or not 1<=digit<base:
        raise ValueError('integer base>=2 and digit in [1,base)')
    if not isinstance(alpha,int) or alpha<1:raise ValueError('integer shape>=1')
    return ((Fraction(1,digit**alpha)-Fraction(1,(digit+1)**alpha))/
            (1-Fraction(1,base**alpha)))

def pareto_leading_digit(base:int,digit:int,alpha:float)->float:
    """Stable shape>0 probability, alpha->0+ tends to Benford's log law."""
    if not isinstance(base,int) or base<2 or not isinstance(digit,int) or not 1<=digit<base:
        raise ValueError('base/digit')
    if not isfinite(alpha) or alpha<=0:raise ValueError('alpha>0')
    num=expm1(-alpha*log(digit))-expm1(-alpha*log(digit+1))
    den=-expm1(-alpha*log(base))
    return num/den

def benford_digit(base:int,digit:int)->float:
    if base<2 or not 1<=digit<base:raise ValueError('base/digit')
    return log1p(1/digit)/log(base)

def pareto_lorenz(u:float,alpha:float)->float:
    """L(u)=1-(1-u)^(1-1/alpha); requires FINITE mean alpha>1."""
    if not isfinite(alpha) or alpha<=1 or not isfinite(u) or not 0<=u<=1:
        raise ValueError('alpha>1; 0<=u<=1')
    return 1-(1-u)**(1-1/alpha)

def pareto_top_share(population_fraction:float,alpha:float)->float:
    """Top t population owns t^(1-1/alpha) of expected income for alpha>1."""
    if not isfinite(alpha) or alpha<=1 or not isfinite(population_fraction) or not 0<=population_fraction<=1:
        raise ValueError('alpha>1; t in [0,1]')
    return population_fraction**(1-1/alpha)

def pareto_gini(alpha:float)->float:
    if not isfinite(alpha) or alpha<=1:raise ValueError('alpha>1')
    return 1/(2*alpha-1)

def shape_for_top_share(population_fraction:float,share:float)->float:
    """Only 0<t<share<1 gives finite-mean Pareto alpha>1."""
    if not (0<population_fraction<share<1):raise ValueError('0<t<share<1')
    return 1/(1-log(share)/log(population_fraction))
