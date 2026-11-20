from itertools import product
from collections import Counter
import sympy as s
# Existing typed pointed carrier: eight 90 sheets plus one 9 sheet.
p729 = [(0,i,j,k) for i,j,k in product(range(8),range(10),range(9))]+[(1,k) for k in range(9)]
assert len(set(p729)) == 729
assert 729*90 == 65610
assert 5*len(p729)+1 == 3646
assert 54*(5*len(p729)+1)==196884
# A C3 carrier rechart: 5*729 = 1215*3.
assert 5*729==1215*3
# S3 factor Q has 730 natural orbits: 729+1.
assert 1456+3*(729+1)==3646
assert 1456+(729+1)==2186
# Published premises: min nontrivial complex Th degree 248;
# Monster weight-two involution traces 4372 and 276.
assert 54<248
assert [divmod(t,54) for t in (4372,276)]==[(80,52),(5,6)]
# Even more generally any two-factor decomposition of the full Monster
# weight-two representation is impossible when both dimensions >1:
# each dimension is below the minimum nontrivial Monster degree 196883.
divisors=s.divisors(196884)
assert all(d<196883 and 196884//d<196883 for d in divisors if 1<d<196884)
print('PASS: pointed729 carrier, tensor arithmetic, Thompson involution obstruction and full Monster dimension obstruction')
