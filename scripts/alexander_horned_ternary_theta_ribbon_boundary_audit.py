#!/usr/bin/env python3
"""Exact ternary meridian genus/minimal ribbon witness.

Source-owned three-child word: [a,b][b,c].
New identity: it is a cyclic conjugate of [b^-1,c^-1 a].
Thus a once-punctured torus, with a theta graph as ribbon spine,
is an algebraically sufficient *mapped surface* source. This is not
an ambient embedded 3D horn-stage construction.

Historical owners: orientable surface boundary presentations,
classical commutator length, Alexander 1924, Hatcher Example 2B.2;
earlier #1254 owns combinatorial 1->3 pants slots.
"""
def reduce_free(w):
    out=[]
    for x in w:
        if out and out[-1]==-x:out.pop()
        else:out.append(x)
    return tuple(out)
def inv(w):
    return tuple(-x for x in reversed(w))
def comm(a,b):
    return reduce_free(a+b+inv(a)+inv(b))
def cyclic_rotate(w,n):
    return w[n:]+w[:n]
def abelian(w):
    return tuple(w.count(i)-w.count(-i) for i in range(1,4))
def ribbon_polygon(word):
    n=len(word);parent=list(range(n))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]
            x=parent[x]
        return x
    def union(i,j):
        parent[find(i)]=find(j)
    for k in range(1,4):
        i=word.index(k);j=word.index(-k)
        union(i,(j+1)%n);union((i+1)%n,j)
    vertices=len(set(find(i) for i in range(n)))
    edges=n//2
    faces=1
    chi=vertices-edges+faces
    genus=(2-chi)//2
    assert (2-chi)%2==0
    return vertices,edges,faces,chi,genus

def audit():
    a=(1,);b=(2,);c=(3,)
    w=reduce_free(comm(a,b)+comm(b,c))
    assert w==(1,2,-1,3,-2,-3)
    target=comm(inv(b),inv(c)+a)
    assert target==(-2,-3,1,2,-1,3)
    assert cyclic_rotate(w,4)==target
    p=w[:4]
    assert reduce_free(inv(p)+w+p)==target
    assert abelian(w)==(0,0,0)
    assert abelian(a+b+c)==(1,1,1)
    assert ribbon_polygon(w)==(2,3,1,0,1)
    assert ribbon_polygon((1,2,-1,-2,3,4,-3,-4))[:4]==(1,4,1,-2)
    assert reduce_free(comm(a,b)+comm(b,c))==w
    print('PASS six-letter w=',w)
    print('PASS [b^-1,c^-1*a]=',target)
    print('PASS conjugator p= a b A c; p^-1 w p = [B,Ca]')
    print('PASS 2-vertex 3-edge one-face ribbon surface: Euler 0, genus 1')
    print('PASS peripheral pants abc != w in abelianisation')
    print('BOUNDARY theta ribbon surface and continuous group map are not an embedded relative wild-horn 3D stage')
if __name__=='__main__':audit()
