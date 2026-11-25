"""Exact full-vector codec regression, not a native Monster acceptance."""
import numpy as np
from itertools import product
from monster3b_conway_exact_crt import normalize,add,scale,require,linear_combination
from monster3b_char0_orbit_weld import K,Z,mat,columns
from monster3b_exact_weight_codec import OrdinaryCodec,coords
from monster3b_linear_weight_frame import WeightFrame

labels=[(0,0,0)]+[(s,x,j) for s,x,j in product((1,2),range(3),range(2))]
n=len(labels)
class Word:
    def __init__(self,p,c):self.p,self.c=tuple(p),tuple(c)
    def __pow__(self,e):
        e%=3
        p=list(range(n));c=[K.one]*n
        for _ in range(e):
            c=[a*self.c[j] for a,j in zip(c,p)];p=[self.p[j] for j in p]
        return Word(p,c)
    def act(self,v):
        a=coords(v,range(n));out=[K.zero]*n
        for i,j in enumerate(self.p):out[j]=a[i]*self.c[i]
        return linear_combination(out,(unit(j) for j in range(n)),n)
def unit(i):
    a=np.zeros(n,dtype=object);a[i]=1
    return normalize(a,np.zeros(n,dtype=object),1)
def word(f):
    a=[f(*v) for v in labels];return Word([labels.index(v) for v,c in a],[c for v,c in a])
z=word(lambda s,x,j:((s,x,j),Z**s))
t=word(lambda s,x,j:((s,(x+1)%3 if s else 0,j),K.one))
b=word(lambda s,x,j:((s,x,j),Z**(s*x)))
F=WeightFrame(lambda v,g:g.act(v),add,scale,Z,K.one,z,[t],[b])
piv={s:[labels.index((s,0,j)) for j in range(2)] for s in (1,2)}
basis={s:[unit(piv[s][0]),add(scale(Z/3,unit(piv[s][0])),scale(K.convert(2)/7,unit(piv[s][1])))] for s in (1,2)}
M={s:columns([coords(u,piv[s]) for u in basis[s]]).inv() for s in (1,2)}
A={s:mat([[K.one,Z**s],[K.convert(2),K.one]]) for s in (1,2)}
C=OrdinaryCodec(F,piv,M,A,{s:a.inv() for s,a in A.items()},lambda s,i:basis[s][i],n)
checks=0
for v in [unit(j) for j in range(n)]+[normalize([j-7 for j in range(n)],[j*j-1 for j in range(n)],19)]:
    w=F.phase(v,0)
    for s,x in product((1,2),F.points):
        c=C.encode(v,s,x);u=C.decode(s,x,c)
        require(C.encode(u,s,x)==c,'weight coordinate inverse');checks+=1
        w=add(w,u)
    require(w==v,'full ambient inverse');checks+=1
# A vector outside the vacuum must not be accepted on the selected minor.
try:C.encode_vacuum(1,unit(labels.index((1,1,0))))
except ValueError:checks+=1
else:raise ValueError('off-vacuum residual accepted')
print({'exact_weight_codec_checks':checks,'dimension':n})
