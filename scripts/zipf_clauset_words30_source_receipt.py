"""Bounded real-source rank head from Clauset/Newman Moby-Dick word-count data.

Source: Aaron Clauset, Cosma R. Shalizi, M. E. J. Newman (2009),
https://aaronclauset.github.io/powerlaws/data/words.txt
Catalogue: https://aaronclauset.github.io/powerlaws/data.htm
Original novel: Herman Melville, Moby-Dick (1851).
Source catalogue attributes the original frequency compilation to M. E. J.
Newman's (2005) work. Our derivative consists ONLY of the first 30 observed
numeric rank counts. It has NOT ingested or verified all 18855 source rows.

Original textual/statistical ownership remains with Melville/Newman/Clauset
and colleagues; this 2026 fixture/diagnostic is source-written by
Johl Brown with OpenAI ChatGPT assistance, not a claimed replication.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from typing import Sequence

SOURCE_URL = "https://aaronclauset.github.io/powerlaws/data/words.txt"
FIRST_30 = (
    14086,6414,6260,4573,4484,4040,2917,2483,2374,1942,
    1792,1744,1711,1683,1674,1604,1581,1493,1372,1297,
    1161,1134,1065,1043,1041,1035,1022,897,882,844,
)
PREFIX_SHA256 = "75e3f03e3bb560bbf5c0ba7d8e09be505897fb9e7e3be1eeb581e991c42474ba"


def prefix_fingerprint(counts:Sequence[int])->str:
    c=tuple(counts)
    if not c or any(type(x) is not int or x<0 for x in c):
        raise ValueError('nonempty integer counts required')
    return sha256(('\n'.join(map(str,c))+'\n').encode('ascii')).hexdigest()


def conditional_head_distribution(counts:Sequence[int])->tuple[Fraction,...]:
    """Masses conditioned on exactly the provided head; NOT full-corpus PMF."""
    c=tuple(counts)
    if not c or any(type(x) is not int or x<0 for x in c) or sum(c)==0:
        raise ValueError('nonempty, nonnegative counts with positive total')
    return tuple(Fraction(v,sum(c)) for v in c)


def rank_head_cdf_distance(counts:Sequence[int],conditional_model:Sequence[Fraction])->Fraction:
    """Exact finite max cumulative discrepancy; descriptive, NOT a KS p-value."""
    observed=conditional_head_distribution(counts)
    model=tuple(conditional_model)
    if (len(model)!=len(observed) or any(not isinstance(x,Fraction) or x<0 for x in model)
            or sum(model,Fraction())!=1):
        raise ValueError('rank-aligned rational normalized model required')
    e=m=distance=Fraction()
    for a,b in zip(observed,model):
        e+=a;m+=b;distance=max(distance,abs(e-m))
    return distance
