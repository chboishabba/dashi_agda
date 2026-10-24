#!/usr/bin/env python3
"""Exact-rational tame-placement sanity check, not a topology proof."""
from fractions import Fraction as Q
from itertools import combinations

L=Q(9); r=Q(1); tube_width=Q(1,8)
tube_start=Q(3,4); tube_end=Q(17,2)
centers=[(L,Q(0),Q(0)),(Q(0),L,Q(0)),(Q(0),Q(0),L)]
center=(Q(0),Q(0),Q(0))
def norm2(a,b):return sum((u-v)**2 for u,v in zip(a,b))
def cycle(p):return (p[2],p[0],p[1])
def tube_box(i):
    return tuple((tube_start,tube_end) if j==i else (-tube_width,tube_width) for j in range(3))
def disjoint_boxes(a,b):return any(x[1]<y[0] or y[1]<x[0] for x,y in zip(a,b))
def sat_envelope(i):return tuple((c-r,c+r) for c in centers[i])
def satellite_vs_foreign_tube(i,j):
    if i==j:raise ValueError('self attachment is intended')
    return disjoint_boxes(sat_envelope(i),tube_box(j))

def check():
    assert cycle(centers[0])==centers[1]
    assert cycle(centers[1])==centers[2]
    assert cycle(centers[2])==centers[0]
    assert cycle(center)==center
    assert all(norm2(center,c)==81 for c in centers)
    assert all(norm2(centers[i],centers[j])==162 for i,j in combinations(range(3),2))
    assert all(norm2(centers[i],centers[j])>4*r*r for i,j in combinations(range(3),2))
    assert all(norm2(center,c)>4*r*r for c in centers)
    assert all(disjoint_boxes(tube_box(i),tube_box(j)) for i,j in combinations(range(3),2))
    assert all(satellite_vs_foreign_tube(i,j) for i in range(3) for j in range(3) if i!=j)
    assert all(not disjoint_boxes(sat_envelope(i),tube_box(i)) for i in range(3))
    assert tube_start < r and tube_end > L-r
    print('C3 satellite permutation and fixed center: PASS')
    print('3 satellite ball envelopes: pairwise separated; center separated: PASS')
    print('3 candidate tube boxes: pairwise disjoint, avoid foreign satellite envelopes: PASS')
    print('Candidate tubes overlap own satellite envelope and central ball: PASS')
    print('Tame cap attachment / collar homeomorphism / van Kampen: NOT TESTED')

if __name__=='__main__':check()
