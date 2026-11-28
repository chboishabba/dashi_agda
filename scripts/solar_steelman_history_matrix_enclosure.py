"""Exact sparse polynomial-ball assembly of the actual reduced delay tangent.
Uses rational metric inverses and rational enclosures of sqrt(2), not the
binary64 analytic tangent as a source of certified coefficients.
"""
import sympy as S
from solar_steelman_history_harmonic_enclosure import Ball,trig,rat,norm,s,ratios
from solar_steelman_boundary_weld import branch

def sqrt2():
    # Consecutive decimal rational bounds checked by squaring.
    lo=S.Rational(1414213562373095048801688724209,10**30)
    hi=lo+S.Rational(1,10**30)
    assert lo**2<2<hi**2
    return Ball((lo+hi)/2,(hi-lo)/2)

def local_trig(lo,hi,w,degree):
    C0,Z0=trig(lo,lo,w,max(96,degree))
    C,Z=trig(0,hi-lo,w,degree)
    return (C0*C-Z0*Z).truncate(degree),(Z0*C+C0*Z).truncate(degree)

def wave(pair,lo,hi,degree,derivative=0):
    C1,Z1=local_trig(lo,hi,1,degree);C2,Z2=local_trig(lo,hi,2,degree)
    a,b=pair[1];c,d=pair[2]
    out=[]
    for i in range(len(a)):
        v=S.expand((1+S.I)*(a[i]+S.I*b[i])*S.I**derivative)
        u=S.expand((c[i]+S.I*d[i])*(2*S.I)**derivative)
        out.append((S.re(v)*C1-S.im(v)*Z1+sqrt2()*(S.re(u)*C2-S.im(u)*Z2)).truncate(degree))
    return out

class Sparse:
    def __init__(self,rows,cols,degree):
        self.rows,self.cols,self.degree=rows,cols,degree;self.data={}
    def add(self,i,j,v):
        if not isinstance(v,Ball):v=Ball(v)
        if v.p==0 and v.e==0:return
        self.data[i,j]=(self.data.get((i,j),Ball(0))+v).truncate(self.degree)
    def block(self,i,j,M,scale=1):
        for r in range(M.rows):
            for c in range(M.cols):
                if M[r,c]!=0:self.add(i+r,j+c,scale*M[r,c])
    def export(self):
        P=S.MutableSparseMatrix(self.rows,self.cols,{k:v.p for k,v in self.data.items() if v.p!=0})
        err=[S.Integer(0)]*self.rows
        for (i,j),v in self.data.items():err[i]+=v.e
        return P,max(err,default=S.Integer(0))

def construct(m,a,lo,hi,degree=8,gain=100,Wstar=100):
    lo,hi,gain,Wstar=map(rat,(lo,hi,gain,Wstar));assert hi>lo and Wstar>0
    d=m['d'];M,N,C,B,H=d['M'],d['N'],d['C'],m['B'],m['H']
    T=d['T'];ts=T[:1,:];tr=T[8:15,:];high,low=a['rows']
    Ls,Ks=branch(S.Integer(2),S.Integer(1),-high['X'][:1,:1])
    Lr,Kr=branch(S.Integer(1),S.Integer(2),-low['X'][8:15,8:15])
    Mi=M.inv();Hi=H.inv()/2;Li=Ls.inv();Lri=Lr.inv()
    n=len(a['models']);E=0;b=M.rows;z=b+N.rows;i=z+H.rows
    q,x,v=i+1,i+2,i+3;j=i+4;Q,X,V=j+7,j+14,j+21
    nc=j+28;size=nc+5*n+4
    e0,e1,h0,h1,p=[nc+k*n for k in range(5)]
    phi,mom,W,heat=range(size-4,size)
    A=Sparse(size,size,degree);D1=Sparse(size,n,degree);D2=Sparse(size,n,degree);R=Sparse(n,size,degree)
    for row,col,mat in [(E,b,Mi*C.T*N),(E,z,-Mi*B),(E,i,Mi*ts.T),(E,j,-Mi*tr.T),(b,E,-C),(z,E,Hi*B.T),
                        (i,E,-Li*ts),(i,i,-Li),(i,q,-Li*Ks),(i,x,-Li),(j,E,Lri*tr),(j,j,-low['load']*Lri),(j,Q,-Lri*Kr),(j,X,-Lri)]:
        A.block(row,col,mat)
    for row,col,dim,scale in [(q,i,1,1),(x,i,1,1),(x,v,1,-1),(v,x,1,1),(Q,j,7,1),(X,j,7,1),(X,V,7,-4),(V,X,7,1)]:
        A.block(row,col,S.eye(dim),scale)
    Z=wave({w:a['data'][w][0] for w in (1,2)},lo,hi,degree)
    rr=[]
    for k,(ids,r,c) in enumerate(a['models']):
        inv,sp=ratios(c,lo,hi,max(96,degree),4)
        inv,sp=inv.truncate(degree),sp.truncate(degree)
        rr.append([(e0+k,inv),(e1+k,inv),(h0+k,sp),(h1+k,-sp)])
        for col,val in rr[-1]:R.add(k,col,val)
        f=wave(r,lo,hi,degree);fp=wave(r,lo,hi,degree,1)
        # Force derivative = f delta ratio + f' delta beat.
        for l,idx in enumerate(ids):
            for row in range(H.rows):
                scale=Hi[row,idx]
                if not scale:continue
                for col,val in rr[-1]:A.add(z+row,col,scale*f[l]*val)
                A.add(z+row,h1+k,scale*fp[l]);A.add(z+row,h0+k,-scale*fp[l])
        power=sum((Z[idx]*f[l] for l,idx in enumerate(ids)),Ball(0))
        pd=sum((Z[idx]*fp[l] for l,idx in enumerate(ids)),Ball(0))
        for row in (e0+k,e1+k):
            for l,idx in enumerate(ids):A.add(row,z+idx,-f[l]*S.Rational(1,2))
            for col,val in rr[-1]:A.add(row,col,-power*val*S.Rational(1,2))
            A.add(row,h1+k,-pd*S.Rational(1,2));A.add(row,h0+k,pd*S.Rational(1,2))
        for row,sgn in ((e0+k,1),(e1+k,-1)):
            A.add(row,e0+k,sp*sgn*S.Rational(1,2));A.add(row,e1+k,-sp*sgn*S.Rational(1,2))
        A.add(h1+k,p+k,1)
    # Instantaneous store exchange cancels exactly against delay replacement.
    # Retain only active directed current launch plus two delayed channels.
    for l in a['order'][1:]:
        k=a['parent'][l];f=a['flows'][l]
        if f==0:raise ValueError("zero-flow kink")
        src,dst,F=(k,l,f) if f>0 else (l,k,-f)
        for row in (e0+src,e1+src):
            for col,val in rr[src]:A.add(row,col,-(F+gain)*val*S.Rational(1,2))
            D1.add(row,dst,-(F-gain)/2)
        for row in (e0+dst,e1+dst):
            D1.add(row,src,(F+gain)/2);D2.add(row,dst,(F-gain)/2)
        for row,sign in ((p+k,1),(p+l,-1)):
            A.add(row,h1+l,sign);A.add(row,h0+l,-sign)
            A.add(row,h1+k,-sign);A.add(row,h0+k,sign)
            A.add(row,p+l,S.Rational(sign,2));A.add(row,p+k,-S.Rational(sign,2))
    tau=[(h1,2),(h0,-2),(phi,-1),(p,1),(mom,-S.Rational(1,2))]
    for col,val in tau:A.add(p,col,-2*val);A.add(mom,col,val)
    A.add(phi,mom,1)
    co,si=local_trig(lo,hi,2,degree)
    drive=sqrt2()*co;phase=-sqrt2()*si
    A.add(i,phi,2*Li[0,0]*phase);A.add(i,W,Li[0,0]*drive*(1/Wstar))
    A.add(W,phi,-2*drive*phase);A.add(W,W,-drive*drive*(1/Wstar))
    return tuple(Y.export() for Y in (A,D1,D2,R))

def fixture():
    lo,hi=S.Rational(0),S.Rational(1,10)
    x=Sparse(2,2,4);x.add(0,0,Ball(s, S.Rational(1,10)));x.add(0,1,2)
    P,e=x.export();assert P[0,0]==s and P[0,1]==2 and e==S.Rational(1,10)
    c,z=local_trig(lo,hi,2,4)
    assert c.p.subs(s,0)==1 and z.p.subs(s,0)==0
    print('PASS sparse matrix enclosure fixture')
if __name__=='__main__':fixture()
