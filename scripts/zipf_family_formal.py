"""Finite source-typed Zipf-family atlas; 27 distinct mathematical surfaces.

All empirical laws/historical examples are observations or hypotheses, never
universal implications of their names. Original historical sources are listed
in Docs/research/zipf_family_formalization_20261027.md.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from math import exp, isfinite, log, log1p
from typing import Mapping, Sequence

class Authority(str, Enum):
    MATHEMATICAL = 'mathematical-identity'
    MODEL = 'parameterized-model'
    EMPIRICAL = 'empirical-diagnostic'
    HYPOTHESIS = 'unverified-hypothesis'
    REPRESENTATION = 'data-representation'
    PROVENANCE = 'attribution-or-evidence'

@dataclass(frozen=True)
class Entry:
    key: str
    name: str
    authority: Authority
    carrier: str
    original_root: str

ATLAS = (
    Entry('zipf','Zipf law',Authority.MODEL,'rank -> mass','Estoup 1916; Zipf 1935/1949'),
    Entry('one_percent','1% participation rule',Authority.HYPOTHESIS,'population -> participation shares','90-9-1 community heuristic'),
    Entry('benford','Benford law',Authority.MODEL,'base -> leading-digit distribution','Newcomb 1881; Benford 1938'),
    Entry('bradford','Bradford scattering law',Authority.EMPIRICAL,'journals -> equal-output zones','Bradford 1934'),
    Entry('brevity','Brevity law',Authority.EMPIRICAL,'frequency × length','Zipf 1949; later quantitative linguistics'),
    Entry('demographic_gravitation','Demographic gravitation',Authority.MODEL,'population pairs × distances','Reilly 1931; Stewart 1940s'),
    Entry('word_list','Word list',Authority.REPRESENTATION,'specified corpus -> frequency table','corpus specific'),
    Entry('gibrat','Gibrat growth law',Authority.HYPOTHESIS,'size time series -> ratios','Gibrat 1931'),
    Entry('hapax','Hapax legomenon',Authority.MATHEMATICAL,'corpus relative singleton','historical philology'),
    Entry('heaps','Heaps/Herdan law',Authority.EMPIRICAL,'prefix -> unique types','Herdan 1960; Heaps 1978'),
    Entry('hilberg','Hilberg hypothesis',Authority.HYPOTHESIS,'block entropy growth','Hilberg 1990; Dębowski later'),
    Entry('historical_recurrence','Historical recurrence',Authority.HYPOTHESIS,'dated coded event recurrence','no single primary universal'),
    Entry('king','King effect',Authority.EMPIRICAL,'top rank outlier','rank size statistics'),
    Entry('long_tail','Long tail',Authority.REPRESENTATION,'remaining probability/share','general probability'),
    Entry('lorenz','Lorenz curve',Authority.MATHEMATICAL,'cumulative share polygon','Max O. Lorenz 1905'),
    Entry('lotka','Lotka law',Authority.EMPIRICAL,'authors -> output-count distribution','A. J. Lotka 1926'),
    Entry('menzerath','Menzerath–Altmann law',Authority.EMPIRICAL,'whole size -> constituent mean','Menzerath; Altmann 1980'),
    Entry('pareto_distribution','Pareto distribution',Authority.MODEL,'positive support -> survival','Vilfredo Pareto 1890s'),
    Entry('pareto_principle','Pareto principle',Authority.EMPIRICAL,'sorted contributors -> top share','Pareto; later 80/20 usage'),
    Entry('price','Price square-root rule',Authority.HYPOTHESIS,'authors -> top sqrt(n) share','D. de Solla Price'),
    Entry('least_effort','Least effort',Authority.HYPOTHESIS,'choices -> cost minimizers','Zipf 1949'),
    Entry('rank_size','Rank–size',Authority.REPRESENTATION,'sorted values','statistical representation'),
    Entry('stigler','Stigler eponymy law',Authority.PROVENANCE,'credited vs original root','Stigler 1980; earlier Merton'),
    Entry('letter_frequency','Letter frequency',Authority.REPRESENTATION,'alphabet and text -> count','corpus specific'),
    Entry('common_english','Most common English words',Authority.REPRESENTATION,'English corpus -> top-K','corpus specific'),
    Entry('zipf_mandelbrot','Zipf–Mandelbrot',Authority.MODEL,'shifted rank -> PMF','Zipf; Mandelbrot 1950s'),
    Entry('hurwitz','Hurwitz zeta',Authority.MATHEMATICAL,'s,q -> series','Adolf Hurwitz'),
)
assert len(ATLAS)==len({x.key for x in ATLAS})==27

def positive(x, name):
    if not isfinite(x) or x<=0:raise ValueError(name)
def nonnegative(x, name):
    if not isfinite(x) or x<0:raise ValueError(name)

def zipf_mandelbrot(n:int,exponent:float,shift:float=0)->tuple[float,...]:
    if not isinstance(n,int) or n<1:raise ValueError('n>=1')
    nonnegative(exponent,'exponent');nonnegative(shift,'shift')
    w=[exp(-exponent*log((r+shift)/(1+shift))) for r in range(1,n+1)]
    z=sum(w)
    return tuple(v/z for v in w)

def finite_hurwitz(s:int,shift:int,n:int)->Fraction:
    if not all(isinstance(v,int) and v>=0 for v in (s,shift,n)):
        raise ValueError('nonnegative integers')
    return sum((Fraction(1,(r+shift)**s) for r in range(1,n+1)),Fraction())

def hurwitz_tail_bound(s:float,q:float,n:int)->tuple[float,float]:
    """Bounds on sum_{r=n+1}^infinity (r+q)^(-s), not on its partial sum.

    For s>1, q>=0, integer n>=1, the decreasing-integrand comparison is
    integral_{n+1}^infinity f <= sum_{r=n+1}^infinity f(r)
    <= integral_n^infinity f.  Neither endpoint is the tail itself.
    Original mathematics: classical integral comparison; DLMF 25.11.
    """
    if (not isfinite(s) or s<=1 or not isfinite(q) or q<0
            or type(n) is not int or n<1):
        raise ValueError('s>1,q>=0,n>=1')
    lower=(q+n+1)**(1-s)/(s-1)
    upper=(q+n)**(1-s)/(s-1)
    return lower, upper

def corpus_counts(tokens:Sequence[str])->Counter[str]:
    return Counter(tokens)
def word_list(tokens:Sequence[str])->tuple[tuple[str,int],...]:
    return tuple(sorted(corpus_counts(tokens).items(),key=lambda p:(-p[1],p[0])))
def hapaxes(tokens:Sequence[str])->tuple[str,...]:
    return tuple(sorted(w for w,c in corpus_counts(tokens).items() if c==1))
def heaps_prefix(tokens:Sequence[str])->tuple[int,...]:
    seen=set();result=[]
    for t in tokens:
        seen.add(t);result.append(len(seen))
    return tuple(result)
def letter_frequencies(text:str,alphabet:str='abcdefghijklmnopqrstuvwxyz')->Counter[str]:
    valid=set(alphabet)
    return Counter(c for c in text.casefold() if c in valid)
def common_words(tokens:Sequence[str],k:int)->tuple[tuple[str,int],...]:
    if k<0:raise ValueError('k>=0')
    return word_list(tokens)[:k]

def benford_first_digit(base:int,d:int)->float:
    if base<2 or d<1 or d>=base:raise ValueError('digit domain')
    return log1p(1/d)/log(base)

def leading_digit(x:float,base:int=10)->int:
    if base<2:raise ValueError('base>=2')
    positive(abs(x),'abs x')
    x=abs(x)
    while x>=base:x/=base
    while x<1:x*=base
    return min(base-1,max(1,int(x)))

def lorenz_curve(values:Sequence[float])->tuple[tuple[float,float],...]:
    if not values or any(not isfinite(v) or v<0 for v in values):
        raise ValueError('nonempty finite nonnegative')
    v=sorted(values);total=sum(v)
    if total<=0:raise ValueError('positive sum')
    c=0.;out=[(0.,0.)]
    for i,x in enumerate(v,1):
        c+=x;out.append((i/len(v),c/total))
    return tuple(out)

def gini(values:Sequence[float])->float:
    p=lorenz_curve(values)
    return 1-sum((b[0]-a[0])*(a[1]+b[1]) for a,b in zip(p,p[1:]))

def top_share(values:Sequence[float],k:int)->float:
    if not values or not 0<=k<=len(values) or any(not isfinite(v) or v<0 for v in values) or sum(values)<=0:
        raise ValueError('nonnegative top k with positive total')
    return sum(sorted(values,reverse=True)[:k])/sum(values)

def long_tail_share(values:Sequence[float],head_count:int)->float:
    return 1-top_share(values,head_count)

def rank_size(values:Sequence[float])->tuple[float,...]:
    if any(not isfinite(v) or v<0 for v in values):raise ValueError('finite nonnegative')
    return tuple(sorted(values,reverse=True))

def king_effect_ratio(values:Sequence[float],s:float=1)->float:
    if len(values)<2 or sorted(values,reverse=True)[1]<=0:raise ValueError('two positive ranks')
    nonnegative(s,'s')
    v=rank_size(values)
    return v[0]/(v[1]*2**s)

def pareto_survival(x:float,x_min:float,alpha:float)->float:
    positive(x_min,'x_min');positive(alpha,'alpha')
    if x<x_min:return 1.
    return (x_min/x)**alpha
def pareto_cdf(x:float,x_min:float,alpha:float)->float:
    return 1-pareto_survival(x,x_min,alpha)

def lotka_pmf(n:int,exponent:float,max_output:int)->float:
    if not 1<=n<=max_output:raise ValueError('support')
    return zipf_mandelbrot(max_output,exponent)[n-1]

def bradford_zone_sizes(core:int,multiplier:float,number_zones:int)->tuple[float,...]:
    if core<1 or number_zones<1:raise ValueError('core,zones')
    positive(multiplier,'multiplier')
    return tuple(core*multiplier**j for j in range(number_zones))

def bradford_empirical_zones(counts:Sequence[int],number_zones:int)->tuple[tuple[int,int],...]:
    if number_zones<1 or not counts or any(not isinstance(x,int) or x<0 for x in counts):
        raise ValueError('journal counts')
    data=sorted(counts,reverse=True);target=sum(data)/number_zones
    out=[];n=0;articles=0
    for v in data:
        if len(out)<number_zones-1 and n>0 and abs(articles-target)<=abs(articles+v-target):
            out.append((n,articles));n=0;articles=0
        n+=1;articles+=v
    out.append((n,articles))
    return tuple(out)

def brevity_pairs(tokens:Sequence[str],lengths:Mapping[str,int])->tuple[tuple[int,int],...]:
    counts=corpus_counts(tokens)
    if any(w not in lengths or lengths[w]<0 for w in counts):raise ValueError('lengths')
    return tuple((lengths[w],counts[w]) for w in sorted(counts))

def menzerath_altmann(n:float,a:float,b:float,c:float)->float:
    positive(n,'n');positive(a,'a')
    if not isfinite(b) or not isfinite(c):raise ValueError('b,c')
    return a*n**b*exp(-c*n)

def demographic_gravity(a:float,b:float,d:float,gamma:float=2)->float:
    nonnegative(a,'a');nonnegative(b,'b');positive(d,'d');nonnegative(gamma,'gamma')
    return a*b/d**gamma

def gibrat_growth_ratios(values:Sequence[float])->tuple[float,...]:
    if len(values)<2:raise ValueError('two periods')
    for v in values:positive(v,'size')
    return tuple(b/a for a,b in zip(values,values[1:]))

def participation_shares(counts:Sequence[int],threshold:int=1)->tuple[float,float]:
    if not counts or threshold<1 or any(not isinstance(v,int) or v<0 for v in counts):
        raise ValueError('participant counts')
    p=sum(v>=threshold for v in counts)/len(counts)
    return p,1-p

def heaps_model(n:float,k:float,beta:float)->float:
    positive(n,'n');positive(k,'k')
    if not 0<=beta<=1:raise ValueError('beta')
    return k*n**beta

def hilberg_model(n:float,c:float,beta:float)->float:
    positive(n,'n');nonnegative(c,'c')
    if not 0<=beta<=1:raise ValueError('beta')
    return c*n**beta

def repeated_event_pairs(events:Sequence[tuple[int,str]])->tuple[tuple[int,int,str],...]:
    return tuple((d,events[j][0],lab) for i,(d,lab) in enumerate(events)
                 for j in range(i+1,len(events)) if events[j][1]==lab)

def price_sqrt_top_count(n:int)->int:
    if n<1:raise ValueError('authors')
    return next(i for i in range(1,n+1) if i*i>=n)

def price_share(publications:Sequence[int])->float:
    if not publications or any(not isinstance(x,int) or x<0 for x in publications) or sum(publications)==0:
        raise ValueError('positive output')
    return top_share(publications,price_sqrt_top_count(len(publications)))

def least_effort_argmins(costs:Mapping[str,float])->tuple[str,...]:
    if not costs or any(not isfinite(v) for v in costs.values()):raise ValueError('costs')
    m=min(costs.values())
    return tuple(sorted(k for k,v in costs.items() if v==m))

@dataclass(frozen=True)
class DiscoveryAttribution:
    label:str
    credited_person:str
    earliest_documented_person:str
    independent_primary_root:str|None=None

def stigler_mismatch(a:DiscoveryAttribution)->bool:
    return a.credited_person!=a.earliest_documented_person

def proof_status(key:str)->Authority:
    return next(x.authority for x in ATLAS if x.key==key)
