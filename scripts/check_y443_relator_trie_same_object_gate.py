#!/usr/bin/env python3
"""Y443 exact 80-relator prefix-trie and S5 extension negative control.

This builds an exact word index, not a complete/confluent group normal form.
"""
from itertools import combinations
from collections import deque

NODES = ("a","b1","c1","d1","e1","b2","c2","d2","e2","b3","c3","d3")
EDGES={frozenset(z) for z in (
 ("a","b1"),("b1","c1"),("c1","d1"),("d1","e1"),
 ("a","b2"),("b2","c2"),("c2","d2"),("d2","e2"),
 ("a","b3"),("b3","c3"),("c3","d3"))}
SPIDER=("a","b1","c1","a","b2","c2","a","b3","c3")
CENTRAL=("a","b3","c3","d3","b1","c1","b2")
ID=(0,1,2,3,4)

def relators():
    words=[("square:"+x,(x,x)) for x in NODES]
    for a,b in combinations(NODES,2):
        edge=frozenset((a,b)) in EDGES
        words.append((("edge:" if edge else "nonedge:")+a+":"+b,
                      (a,b)*(3 if edge else 2)))
    return words+[("spider",SPIDER*10),("central",CENTRAL*9)]

def trie(words):
    t=[{"children":{},"terminal":()}]
    for name,word in words:
        cur=0
        for x in word:
            nxt=t[cur]["children"]
            if x not in nxt:
                nxt[x]=len(t)
                t.append({"children":{},"terminal":()})
            cur=nxt[x]
        t[cur]["terminal"]+=(name,)
    return t

def query(t,word):
    cur=0
    for x in word:
        cur=t[cur]["children"].get(x,-1)
        if cur<0:return ()
    return t[cur]["terminal"]

def compose(p,q):
    return tuple(p[q[i]] for i in range(5))

def evalword(w,imgs):
    p=ID
    for x in w:p=compose(p,imgs[x])
    return p

def check():
    words=relators()
    assert len(words)==80 and sum(len(w) for _,w in words)==463
    t=trie(words)
    assert len(t)==394
    assert all(query(t,w)==(n,) for n,w in words)
    assert all(query(t,w+("a",))==() for _,w in words)
    trivial={x:ID for x in NODES}
    assert all(evalword(w,trivial)==ID for _,w in words)

    path=("b2","c2","d2","e2")
    trans=[]
    for k in range(4):
        p=list(ID);p[k],p[k+1]=p[k+1],p[k];trans.append(tuple(p))
    imgs={x:ID for x in NODES}
    imgs.update(dict(zip(path,trans)))
    for x in path:assert compose(imgs[x],imgs[x])==ID
    for x,y in combinations(path,2):
        z=compose(imgs[x],imgs[y])
        power=3 if abs(path.index(x)-path.index(y))==1 else 2
        result=ID
        for _ in range(power):result=compose(result,z)
        assert result==ID
    fails=[n for n,w in words if evalword(w,imgs)!=ID]
    assert fails==["edge:a:b2","spider","central"],fails

    u=(1,2,3,4,0);v=(1,0,2,3,4)
    seen={ID:()};todo=deque([ID])
    while todo:
        g=todo.popleft()
        for label,x in (("u",u),("v",v)):
            h=compose(g,x)
            if h not in seen:
                seen[h]=seen[g]+(label,);todo.append(h)
    assert len(seen)==120
    print("PASS Y443: 80 exact relators / 463 letters / 394 trie nodes")
    print("PASS Y443: 80 original relator lookups, trivial S5 action")
    print("PASS A4: 10 Coxeter relations and 120-element two-generator S5")
    print("PASS no-go: A4-on-path fails precisely edge:a:b2, spider, central")
    print("SCOPE: trie is not a Monster word normalizer or FLM/VOA isomorphism")

if __name__=="__main__":
    check()
