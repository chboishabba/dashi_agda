#!/usr/bin/env python3
"""Exact rational same-panel trend difference for *derived annual series* only.

Input CSV: year,weight,before,after. Every year must occur once, all values
must be present, weights fixed and strictly positive. The caller must establish
that both columns are comparably processed climate products; this code CANNOT
infer national ACORN-SAT impact from raw CDO edits or site counts.
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
import json
from pathlib import Path

FIELDS = ('year','weight','before','after')

def parse(text):
    rows=[]
    rdr=csv.DictReader(text.splitlines())
    if tuple(rdr.fieldnames or ()) != FIELDS:
        raise ValueError('expected year,weight,before,after header')
    seen=set()
    for i,r in enumerate(rdr,2):
        if None in r or any(r.get(k) is None or not r[k].strip() for k in FIELDS):
            raise ValueError(f'partial or ambiguous panel row {i}')
        try:
            year=int(r['year'])
            if str(year) != r['year'].strip():
                raise ValueError('noncanonical year')
            w,a,b=[Fraction(r[k]) for k in ('weight','before','after')]
        except (ValueError,ZeroDivisionError) as exc:
            raise ValueError(f'invalid numeric data at line {i}') from exc
        if w<=0 or year in seen:
            raise ValueError(f'non-positive weight or duplicate year at {i}')
        seen.add(year)
        rows.append((year,w,a,b))
    if len(rows)<2:
        raise ValueError('at least two distinct years required')
    return sorted(rows)

def fraction_text(x):
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'

def analyze(rows):
    total=sum((w for _,w,_,_ in rows), Fraction(0))
    center=sum((w*year for year,w,_,_ in rows), Fraction(0))/total
    denom=sum((w*(year-center)**2 for year,w,_,_ in rows),Fraction(0))
    if denom<=0: raise ValueError('years have zero weighted variance')
    a=sum((w*(year-center)*before for year,w,before,_ in rows),Fraction(0))/denom
    b=sum((w*(year-center)*after for year,w,_,after in rows),Fraction(0))/denom
    exact_diff=sum((w*(year-center)*(after-before) for year,w,before,after in rows),Fraction(0))/denom
    if b-a!=exact_diff: raise AssertionError('linear slope identity failed')
    absolute_bound=sum((abs(w*(year-center)*(after-before)) for year,w,before,after in rows),Fraction(0))/denom
    return {'schema':'dashi.bom.same_panel_trend.v1',
            'years':len(rows),'first_year':rows[0][0],'last_year':rows[-1][0],
            'trend_before_C_per_decade':float(10*a),
            'trend_after_C_per_decade':float(10*b),
            'trend_difference_C_per_decade':float(10*exact_diff),
            'exact_difference_C_per_decade':fraction_text(10*exact_diff),
            'absolute_change_bound_C_per_decade':float(10*absolute_bound),
            'same_annual_years_and_weights': True,
            'homogenisation_recomputed': False,
            'raw_archive_causation_established': False,
            'national_trend_claim_authorised': False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--annual-panel',type=Path,required=True)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    result=analyze(parse(args.annual_panel.read_text(encoding='utf-8')))
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(data,encoding='utf-8')
    else: print(data,end='')

if __name__ == '__main__': main()
