"""Original-character Fourier trace identity, reduced exact cyclotomic control."""
from itertools import product
from sympy import QQ
from monster3b_single_residual_frame import trace_vacuum

K=QQ.cyclotomic_field(3); zeta,one,zero=K.unit,K.one,K.zero
class Word:
    def __init__(self,p,c):self.p,self.c=tuple(p),tuple(c)
    def __mul__(self,b):return Word([b.p[j] for j in self.p],[self.c[i]*b.c[j] for i,j in enumerate(self.p)])
    def __pow__(self,n):
        r=Word(range(len(self.p)),[one]*len(self.p))
        for _ in range(n):r=r*self
        return r
    def trace(self):return sum((c for i,c in enumerate(self.c) if self.p[i]==i),zero)

def run():
    labels=[(0,0,0)]+[(s,x,i) for s in (1,2) for x in range(3) for i in range(2)]
    def word(f):
        a=[f(*v) for v in labels];return Word([labels.index(v) for v,c in a],[c for v,c in a])
    z=word(lambda s,x,i:((s,x,i),zeta**s)); b=word(lambda s,x,i:((s,x,i),zeta**(s*x)))
    # Zero-affine diagonal quadratic phase. Its vacuum entry is one, but
    # the ambient trace mixes central phases and the fixed sector.
    g=word(lambda s,x,i:((s,x,i),zeta**(s*(x*x+i))))
    J=word(lambda s,x,i:((s,(-x)%3,i),-one if s and i==0 else one))
    count=0
    for s,k in product((1,2),range(3)):
        a=trace_vacuum(Word.trace,z,[b],g**k,zeta,one,s,one)
        d=trace_vacuum(Word.trace,z,[b],g**k*J,zeta,one,s,one)
        if a!=one+zeta**(s*k) or (a-d)/(2*one)!=one or (a+d)/(2*one)!=zeta**(s*k):raise ValueError('trace or constituent projection')
        count+=3
    # A zero trace on a nontrivial phase must be preserved.
    h=word(lambda s,x,i:((s,x,i),(-one if i else one) if s else one))
    for s in (1,2):
        if trace_vacuum(Word.trace,z,[b],h,zeta,one,s,one)!=zero:raise ValueError('zero trace lost')
        count+=1
    print({'exact_trace_checks':count})
if __name__=='__main__':run()
