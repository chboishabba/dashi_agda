#!/usr/bin/env python3
"""Exact Nielsen basis comparison for the ternary horn meridian.
F3=<a,b,c>; u=b^-1, v=c^-1*a, z=c is a free basis.
The inverse map is a=z*v, b=u^-1, c=z.
Source theorem is w=[a,b][b,c] conjugate to [u,v].
A free-group basis change is NOT an ambient collar / handle slide receipt.
"""
from itertools import product
def red(w):
    q=[]
    for x in w:
        if q and q[-1]==-x:q.pop()
        else:q.append(x)
    return tuple(q)
def inv(w):return tuple(-x for x in w[::-1])
def eval_word(w,m):
    return red(tuple(t for x in w for t in (m[abs(x)] if x>0 else inv(m[abs(x)]))))
def comm(a,b):return red(a+b+inv(a)+inv(b))
def check():
    # Original generators a,b,c -> new basis u,v,z
    original_as_new={1:(3,2),2:(-1,),3:(3,)}
    # New generators u,v,z -> original a,b,c
    new_as_original={1:(-2,),2:(-3,1),3:(3,)}
    for i in (1,2,3):
        assert eval_word(original_as_new[i],new_as_original)==(i,)
        assert eval_word(new_as_original[i],original_as_new)==(i,)
    W=red(comm((1,),(2,))+comm((2,),(3,)))
    u,v=new_as_original[1],new_as_original[2]
    p=(1,2,-1,3)
    assert red(inv(p)+W+p)==comm(u,v)
    count=0
    alphabet=(-3,-2,-1,1,2,3)
    for n in range(6):
        for w in product(alphabet,repeat=n):
            w=red(w)
            assert eval_word(eval_word(w,original_as_new),new_as_original)==w
            assert eval_word(eval_word(w,new_as_original),original_as_new)==w
            count+=1
    print('PASS finite all words <=5, including unreduced inputs',count)
    print('PASS explicit free basis and both Nielsen inverse substitutions')
    print('PASS conjugator p=a b A c and [u,v] with u=B, v=C a')
    print('BOUNDARY no homeomorphism / tame handle-slide realization in selected wild stages')
if __name__=='__main__':check()
