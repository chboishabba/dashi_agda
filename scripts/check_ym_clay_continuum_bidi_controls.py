#!/usr/bin/env python3
"""Exact BIDI falsifiers for same-Wilson 4D continuum proof candidates.

Passing only checks finite rational consistency. No source ownership,
Agda, continuum, physical OS, group quantifier or Clay proof is implied.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations
import json

def determinant(a):
    n=len(a); answer=Q(0)
    for p in permutations(range(n)):
        parity=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=Q(-1 if parity%2 else 1)
        for i,j in enumerate(p): term*=a[i][j]
        answer+=term
    return answer

def hankel_psd(c,n):
    if n<1 or len(c)<2*n-1:
        raise ValueError('insufficient transfer moments')
    h=[[Q(c[i+j]) for j in range(n)] for i in range(n)]
    return all(determinant([[h[i][j] for j in indices] for i in indices])>=0
               for size in range(1,n+1)
               for indices in combinations(range(n),size))

def uniform_physical_decay(c,C,q,ell):
    C,q,ell=Q(C),Q(q),Q(ell)
    assert ell>0 and C>=0 and 0<=q<1
    assert all(0<=Q(value)<=C*q**time for time,value in enumerate(c))
    return True

def charge_survival(charges,losses,eta,budget):
    charges=list(map(Q,charges)); losses=list(map(Q,losses))
    eta,budget=Q(eta),Q(budget)
    assert eta>0 and len(charges)==len(losses)+1
    assert charges[0]>=eta+budget
    total=Q(0)
    for n,value in enumerate(charges):
        assert total<=budget and value>=eta
        if n<len(losses):
            assert value<=charges[n+1]+losses[n]
            total+=losses[n]
    return True

def same_source(receipt):
    expected=('finite_wilson','continuum_limit',
              'os_hamiltonian','marked_j_family')
    return all(receipt.get(k) for k in expected) and len(
        {receipt[k] for k in expected})==1

def rejects(fn):
    try:
        assert fn()
    except (AssertionError, ValueError):
        return True
    raise AssertionError('unsound finite BIDI fixture promoted')

def selftest():
    q=Q(1,2)
    correlations=[q**n for n in range(9)]
    assert hankel_psd(correlations,4)
    assert uniform_physical_decay(correlations,1,q,1)
    losses=[Q(1,64)*q**n for n in range(128)]
    charges=[Q(7,128)]
    for loss in losses: charges.append(charges[-1]-loss)
    assert charge_survival(charges,losses,Q(1,64),Q(1,32))
    src=dict.fromkeys(('finite_wilson','continuum_limit',
                       'os_hamiltonian','marked_j_family'),'original-Wilson')
    assert same_source(src)
    bad={
      'positive_entries_not_OS':lambda:hankel_psd(
        [Q(1),Q(1,2),Q(1,10),Q(1,20),Q(1,40)],3),
      'stagewise_gap_not_uniform':lambda:uniform_physical_decay(
        [Q(1,2),Q(1,2),Q(1,2)],1,Q(1,2),1),
      'Gaussian_fourth_cumulant_zero':lambda:charge_survival(
        [Q(0),Q(0)],[Q(0)],Q(1,64),Q(1,32)),
      'excessive_RG_loss':lambda:charge_survival(
        [Q(7,128),Q(0)],[Q(7,128)],Q(1,64),Q(1,32)),
      'different_H_source':lambda:same_source(
        {**src,'os_hamiltonian':'independent-H'}),
      'raw_perimeter_collapse':lambda:charge_survival(
        [Q(1,16),Q(1,256)],[Q(15,256)],Q(1,32),Q(1,32)),
      'wrong_physical_time_units':lambda:uniform_physical_decay(
        [Q(1),Q(1,2)],1,Q(1,2),0)}
    assert all(rejects(fn) for fn in bad.values())
    return {'status':'PASS_REFERENCE_ONLY','OS_Hankel':'4x4 rational PSD',
      'correlation_points':len(correlations),
      'noncollapse_RG_refinements':len(losses),
      'rejected_false_positive_fixtures':list(bad),
      'physical_suN_or_all_G_verified':False,
      'continuum_exists_proved':False,
      'Clay_mass_gap_proved':False}

if __name__=='__main__':
    print(json.dumps(selftest(),indent=2))
