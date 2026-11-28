"""Exact R236 signed block consumer; tags/rates/work supplied by original owner.
No physical estimate or kernel certification. Preserve zero-work incidences.
"""
from itertools import combinations, combinations_with_replacement, product
from random import Random
import sympy as s

BLOCKS = tuple(combinations_with_replacement(range(3), 2))

def moments(rows):
    m = [[0, 0, 0, 0] for _ in range(3)]
    for tag, r, w in rows:
        a = m[tag]
        a[0] += 1; a[1] += r; a[2] += w; a[3] += r*w
    return m

def signed_fold(rows):
    m = moments(rows)
    out = {}
    for a,b in BLOCKS:
        n,r,w,v = m[a]; N,R,W,V = m[b]
        out[a,b] = r*w-n*v if a==b else r*W+R*w-N*v-n*V
    return out

def explicit(rows):
    out = dict.fromkeys(BLOCKS, 0)
    for (a,r,w),(b,R,W) in combinations(rows,2):
        out[tuple(sorted((a,b)))] -= (r-R)*(w-W)
    return out

def check(rows):
    got, want = signed_fold(rows), explicit(rows)
    assert all(s.expand(got[k]-want[k])==0 for k in BLOCKS)
    assert s.expand(sum(got.values()) - (sum(r for _,r,w in rows)*sum(w for _,r,w in rows)-len(rows)*sum(r*w for _,r,w in rows)))==0

if __name__ == '__main__':
    r=s.symbols('r:4'); w=s.symbols('w:4')
    for tags in product(range(3),repeat=4):
        check(list(zip(tags,r,w)))
    rng=Random(236)
    for n in range(65):
        for _ in range(8):
            rows=[(rng.randrange(3),s.Rational(rng.randrange(20),rng.randrange(1,8)),s.Rational(rng.randrange(-20,21),rng.randrange(1,8))) for i in range(n)]
            check(rows)
    # A zero-work incidence can still contribute to the pair difference.
    rows=[(0,1,2),(1,3,0)]
    assert signed_fold(rows)[0,1]==4
    assert signed_fold(rows[:1])[0,1]==0
    # The moments do not recover individual rates, let alone geometry.
    assert moments([(0,0,0),(0,2,0)])==moments([(0,1,0),(0,1,0)])
    print('PASS: 81 symbolic tag assignments; 520 exact rational fibres; six blocks and global sum; two negative controls')
