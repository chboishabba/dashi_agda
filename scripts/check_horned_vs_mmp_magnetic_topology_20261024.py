#!/usr/bin/env python3
"""Horned S2 complement versus magnetic R x S2 topology: source bounded finite audit.

Alexander duality and Hatcher's nontrivial wild complement are *external theorems*,
NOT proved by this script. The actual C3 three-arm geometry/pi1 map in PR #1244
still has open collar and kernel-proof obligations. A5 is a *finite quotient actor*.
"""
from sympy.combinatorics import Permutation, PermutationGroup
# Alexander duality in S3 for ANY embedded S2, including wild:
# reduced H_i(S3 - S2) = reduced H^(2-i)(S2).
coh={0:0,1:0,2:1}
hom={i:coh.get(2-i,0) for i in (0,1,2)}
assert hom=={0:1,1:0,2:0}
# Thus 2 complementary components, each H1=H2=0. By UCT H^2=0 too.
# No flat U1 character or nontrivial first Chern class is forced by horns.
horned={'H1':0,'H2':0,'chern_class_rank':0}
two_mouth={'H1':0,'H2':1,'chern_class_rank':1}  # spatial R x S2
three_balls={'H1':0,'H2':3}  # R3 minus 3 disjoint closed balls
assert horned['H2']!=two_mouth['H2']
assert three_balls['H1']==0
# Independently: A5 finite, non-Abelian, perfect actor. Does NOT prove
# same object as the true geometric horned exterior or a spin/SU2 lift.
A5=PermutationGroup(Permutation(0,1,2),Permutation(0,1,2,3,4))
assert A5.order()==60 and A5.derived_subgroup().order()==60
assert Permutation(0,1,2).order()==3
print('PASS: horn complement acyclic by Alexander duality vs R x S2 H2=Z')
print('PASS: non-Abelian perfect A5 example has a genuine C3 actor')
print('OPEN: geometric pi1, wild smooth spectral problem, SU2/spin lift, induced fermion stress')
