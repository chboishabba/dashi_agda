#!/usr/bin/env python3
"""Exact free-word normal-form witness for a three-child alternative tower.

Source mathematical ownership: free-group normal form; Hatcher Ex.2B.2
owns the DIFFERENT original two-child punctured-torus geometry.
DASHI owns this chosen three-child algebraic comparison, NOT an
Alexander ambient embedding, a group-colimit kernel certificate,
or a physically calibrated gate-depth law.
"""
from random import Random
from itertools import product
import json

def inverse(word):
    return tuple((-gen for gen in reversed(word)))

def reduce_free(word):
    result=[]
    for g in word:
        if result and result[-1]==-g: result.pop()
        else: result.append(g)
    return tuple(result)

def generator_child_word(i):
    # Generators are 1-indexed to encode inverses with signed integers.
    # For source generator i, the three disjoint target children are:
    a,b,c=3*i-2,3*i-1,3*i
    return reduce_free((a,b,-a,-b,b,c,-b,-c))

def expand(word):
    result=[]
    for g in word:
        image=generator_child_word(abs(g))
        result.extend(image if g>0 else inverse(image))
    return reduce_free(result)

def rotate_index(i,depth):
    width=3**depth
    j=i-1
    sector,offset=divmod(j,width)
    return ((sector+1)%3)*width+offset+1

def rotate_word(word,depth):
    return tuple((1 if x>0 else -1)*rotate_index(abs(x),depth) for x in word)

def random_reduced_word(rng,ngen,length):
    result=[]
    while len(result)<length:
        g=rng.randint(1,ngen)*(1 if rng.randrange(2) else -1)
        if result and result[-1]==-g: continue
        result.append(g)
    return tuple(result)

def audit(trials=7000):
    for i in range(1,37):
        w=generator_child_word(i)
        assert len(w)==6 and w==(3*i-2,3*i-1,-(3*i-2),3*i,-(3*i-1),-3*i)
        assert CounterAbelian(w)=={}
    rng=Random(20261028)
    tests=0
    for depth in range(4):
        ngen=3*3**depth
        for _ in range(trials//4):
            word=random_reduced_word(rng,ngen,rng.randrange(1,18))
            image=expand(word)
            assert len(image)==6*len(word)
            assert reduce_free(image)==image
            assert expand(rotate_word(word,depth))==rotate_word(image,depth+1)
            assert CounterAbelian(image)=={}
            tests+=1
    v=(1,)
    sizes=[len(v)]
    for n in range(5):
        v=expand(v)
        sizes.append(len(v))
        assert len(v)==6**(n+1)
    assert len(expand((1,1,1)))==18
    # Falsifier: "three children" alone does NOT give perfection.
    assert CounterAbelian((1,2,3))=={1:1,2:1,3:1}
    return dict(status='PASS',trials=tests,root_expanded_lengths=sizes,
      source_rank='3 * 3^n',
      generator_word='[a,b][b,c] freely reduces to a b A c B C',
      all_stage_map_injection='normal-form paper proof; tests corroborate',
      direct_limit_abelianization='zero by commutator bonding',
      exact_ambient_wild_embedding=False,agda_kernel_typechecked=False)

def CounterAbelian(word):
    values={}
    for x in word:
        g=abs(x)
        values[g]=values.get(g,0)+(1 if x>0 else -1)
    return {g:v for g,v in values.items() if v!=0}

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
