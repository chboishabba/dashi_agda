"""Exact Q(zeta3) signed multiweight controls, NOT actual Monster execution."""
from itertools import product
from sympy import QQ
from monster3b_linear_weight_frame import WeightFrame

K = QQ.cyclotomic_field(3)
Z, I, O = K.unit, K.one, K.zero


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


class Word:
    def __init__(self, p, c):
        self.p, self.c = tuple(p), tuple(c)

    def __mul__(self, b):
        return Word([b.p[j] for j in self.p], [self.c[i]*b.c[j] for i,j in enumerate(self.p)])

    def __pow__(self, n):
        if n < 0:
            p = [0]*len(self.p)
            for i,j in enumerate(self.p): p[j] = i
            return Word(p, [I/self.c[i] for i in p])**(-n)
        r = Word(range(len(self.p)), [I]*len(self.p))
        for _ in range(n): r = r*self
        return r

    def act(self, v):
        out = [O]*len(v)
        for i,j in enumerate(self.p): out[j] = self.c[i]*v[i]
        return tuple(out)


def run():
    pts = tuple(product(range(3), repeat=2))
    labels = [(0,(0,0),0)] + [(s,x,i) for s in (1,2) for x in pts for i in (0,1)]
    def word(f):
        pairs = [f(*a) for a in labels]
        return Word([labels.index(a) for a,c in pairs], [c for a,c in pairs])
    z = word(lambda s,x,i: ((s,x,i), Z**s))
    T = [word(lambda s,x,i: ((s,tuple((t+(s!=0 and j==a))%3 for j,t in enumerate(x)),i),I)) for a in range(2)]
    B = [word(lambda s,x,i: ((s,x,i),Z**(s*x[a]))) for a in range(2)]
    C = word(lambda s,x,i: ((3-s if s else 0,(-x[1]%3,x[0]),i), -I if s==2 and i==0 else I))
    add = lambda v,w: tuple(a+b for a,b in zip(v,w))
    scale = lambda c,v: tuple(c*a for a in v)
    F = WeightFrame(lambda v,g:g.act(v),add,scale,Z,I,z,T,B)
    zero = tuple(O for _ in labels)
    checks = {'roundtrips':0,'orthogonality':0,'signed':0,'linearity':0}
    for j in range(len(labels)):
        v = tuple(I if i==j else O for i in range(len(labels)))
        a, b = F.recover(v)
        require(F.evaluate(a,b)==v,'ambient inverse')
        require(F.recover(F.evaluate(a,b))==(a,b),'coordinate inverse')
        checks['roundtrips']+=2
        for s in (1,2):
            for x,u in zip(pts,b[s]):
                require(u==F.vacuum(u,s),'vacuum range')
                require(F.recover_weight(F.translate(u,x),s,x)==u,'weight inverse')
                checks['orthogonality']+=2
    v = tuple((j-17)*I+(j%3)*Z for j in range(len(labels)))
    w = tuple((j%5)*I-j*Z for j in range(len(labels)))
    a,b=F.recover(v); c,d=F.recover(w)
    e,f=F.recover(add(v,scale(Z,w)))
    require(e==add(a,scale(Z,c)),'zero sector linearity')
    for s in (1,2):
        for j in range(len(pts)):
            require(f[s][j]==add(b[s][j],scale(Z,d[s][j])),'coordinate linearity')
            checks['linearity']+=1
        u=b[s][0]; dest=3-s
        cu=F.hom(u,s,dest,C,I)
        require(F.hom(cu,dest,s,C,I)==F.hom(u,s,s,C**2,I),'outer square')
        require(F.hom(cu,dest,s,C**-1,I)==u,'outer reverse')
        a12,a78=F.split(u,s,C**2)
        require(add(a12,a78)==u and F.split(a12,s,C**2)==(a12,zero) and F.split(a78,s,C**2)==(zero,a78),'signed split')
        require(F.split(cu,dest,C**2)==(F.hom(a12,s,dest,C,I),F.hom(a78,s,dest,C,I)),'outer split covariance')
        checks['signed']+=4
    require(F.evaluate(*F.recover(v))==v,'mixed multiweight and zero roundtrip')
    checks['roundtrips']+=1
    try: F.hom(v,1,2,C,O)
    except ValueError: pass
    else: raise ValueError('zero coefficient accepted')
    print(checks)

if __name__=='__main__': run()
