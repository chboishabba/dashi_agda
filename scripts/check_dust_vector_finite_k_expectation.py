#!/usr/bin/env python3
"""Exhaustive exact-rational vector-affine Dust population-centering expectation.
Original algorithm attribution: Dahal, Mandal, Gülbahar, Vegesna (2026).
DASHI finite audit; not Gaussian sampling or GPU training.
"""
from fractions import Fraction as F
from itertools import product
import json

def affine_credit(draws, grad):
    k, d = len(draws), len(grad)
    mean = [sum((v[j] for v in draws), F(0))/k for j in range(d)]
    return [sum((sum((grad[j]*(a[j]-mean[j]) for j in range(d)), F(0))*a[i] for a in draws), F(0))/k for i in range(d)]

def main():
    receipt={}
    for d,k in [(1,2),(2,2),(2,3),(3,3),(3,4)]:
        directions=list(product((F(-1),F(1)),repeat=d))
        gradient=[F(i+1) for i in range(d)]
        accum=[F(0)]*d
        count=0
        for draws in product(directions,repeat=k):
            value=affine_credit(draws,gradient)
            accum=[x+y for x,y in zip(accum,value)]
            count+=1
        actual=[x/count for x in accum]
        expected=[F(k-1,k)*x for x in gradient]
        assert actual==expected,(d,k,actual,expected)
        receipt[f"{d}D_K{k}"]={"population_count":count,"mean_credit":list(map(str,actual))}
    print(json.dumps(receipt,indent=2))

if __name__=="__main__":main()
