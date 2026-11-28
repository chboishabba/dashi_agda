"""Countercontrol: full residual injection and dense simultaneous
sensitivity do not force superlinear shared bounded-degree DAG cost.
Classical parity and reversible Toffoli maps, no SAT oracle."""
from itertools import product
from collections import Counter

def circuit(n):
    assert n>=2 and n%2==0
    gates=[]
    def gate(op,*args):
        gates.append((op,args));return n+len(gates)-1
    z=list(range(n))
    for i in range(0,n-2,3):
        z[i+2]=gate('xor',z[i+2],gate('and',z[i],z[i+1]))
    p=z[0]
    for v in z[1:]:p=gate('xor',p,v)
    def copies(v,k):
        if k==1:return [v]
        a=gate('copy',v);b=gate('copy',v)
        return copies(a,k//2)+copies(b,k-k//2)
    out=[gate('xor',a,b) for a,b in zip(z,copies(p,n))]
    degree=Counter(i for _,args in gates for i in args)
    assert max(degree.values())<=3 and len(gates)<=5*n
    return gates,out

def evaluate(x,gates,out):
    v=list(x)
    for op,a in gates:
        v.append(v[a[0]] if op=='copy' else v[a[0]]^v[a[1]] if op=='xor' else v[a[0]]&v[a[1]])
    return tuple(v[i] for i in out)

def inverse(y):
    p=sum(y)%2;z=[a^p for a in y]
    for i in range(0,len(y)-2,3):z[i+2]^=z[i]&z[i+1]
    return tuple(z)

def main():
    count=0;controls=[]
    for n in (2,4,6,8,10,12,128,1024):
        gates,out=circuit(n)
        if n<=12:
            Y=set()
            for x in product(range(2),repeat=n):
                y=evaluate(x,gates,out);assert inverse(y)==x;Y.add(y);count+=1
            assert len(Y)==2**n
        zero=evaluate((0,)*n,gates,out);assert zero==(0,)*n
        sens=[0]*n
        for j in range(n):
            x=tuple(int(i==j) for i in range(n));y=evaluate(x,gates,out)
            assert inverse(y)==x
            for i in range(n):sens[i]+=y[i]!=zero[i]
        assert sens==[n-1]*n
        controls.append(dict(n=n,gates=len(gates),edges=sum(len(a) for _,a in gates),sensitivity_each=n-1,distinct_residuals='2^'+str(n)))
    print(dict(exhaustive_roundtrips=count,controls=controls))
if __name__=='__main__':main()
