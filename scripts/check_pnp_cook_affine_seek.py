"""Arithmetic seek on the original Cook prefix-token layout.
Local rejected-row templates are inputs from the original fixed machine.
No generated truth-table oracle, no full tableau or unary token stream.
See CNFCookPrefixTokenExact, ConcreteTapeRawGlobalWindowCNFExact,
ConcreteTapeEndpointCNFExact and ConcreteTapeTimeBudgetPaddingExact.
"""
from itertools import accumulate

# Each literal is (zero-based Fin index, positive). Each clause includes
# AND, OR per literal, optional NEG, VAR, unary index, ZERO, final FALSE.
def literal_tokens(v,pos):return (7,)+(() if pos else (5,))+(2,)+(1,)*v+(0,)
def literal_at(v,pos,k):
    if k==0:return 7
    k-=1
    if not pos:
        if k==0:return 5
        k-=1
    if k==0:return 2
    return 1 if k<=v else 0

def clause_at(clause,k):
    if k==0:return 6
    k-=1
    for v,pos in clause:
        L=v+3+int(not pos)
        if k<L:return literal_at(v,pos,k)
        k-=L
    assert k==0
    return 3

def seek(count,prefix,k):
    """Find unique i with prefix(i)<=k<prefix(i+1)."""
    assert 0<=k<prefix(count);a=0;b=count
    while a+1<b:
        m=(a+b)//2
        if prefix(m)<=k:a=m
        else:b=m
    return a,k-prefix(a)

def triangle(n):return n*(n-1)//2

class CookSeek:
    def __init__(self,T,cell_width,rule_width,transition,acceptance,blank,middle):
        self.T=T;self.w=cell_width;self.r=rule_width;self.trans=tuple(map(tuple,transition));self.acc=tuple(map(tuple,acceptance));self.blank=tuple(blank);self.middle=tuple(middle)
        if T<0 or min(self.w,self.r)<1 or len(self.blank)!=self.w or len(self.middle)%self.w or len(self.middle)<3*self.w:raise ValueError('layout')
        if any(x not in (0,1) for x in self.blank+self.middle):raise ValueError('bits')
        self.C=2*T+len(self.middle)//self.w;self.R=self.C*self.w;self.S=(T+1)*self.R;self.G=self.S+T*self.r
        self.J=max(0,self.C-2)
        for F,N in ((self.trans,self.r+6*self.w),(self.acc,1+self.w)):
            if any(not 0<=i<N or b not in (0,1) for c in F for i,b in c):raise ValueError('template')
        # Precompute sums of affine coordinate coefficients for one block.
        self.ta,self.tb,self.tc=self.coeffs(self.trans,self.trans_coord)
        self.aa,self.ab,self.ac=self.coeffs(self.acc,self.acc_coord)
        self.zblank=tuple(accumulate((int(not b) for b in self.blank),initial=0));self.zmiddle=tuple(accumulate((int(not b) for b in self.middle),initial=0))
    def trans_coord(self,i,t,j):
        if i<self.r:return self.S+t*self.r+i
        q,d=divmod(i-self.r,self.w)
        return (t+q//3)*self.R+(j+q%3)*self.w+d
    def acc_coord(self,i,t,j):
        return self.G+j if i==0 else self.T*self.R+j*self.w+i-1
    def coeffs(self,F,coord):
        a=b=0;c=2*len(F)
        for clause in F:
            for i,pos in clause:
                v=coord(i,0,0);a+=coord(i,1,0)-v;b+=coord(i,0,1)-v;c+=v+3+int(not pos)
        return a,b,c
    def transition_prefix(self,t):return self.J*(self.ta*triangle(t)+self.tc*t)+self.tb*t*triangle(self.J)
    def window_prefix(self,t,j):return j*(self.ta*t+self.tc)+self.tb*triangle(j)
    def acceptance_prefix(self,j):return self.ac*j+self.ab*triangle(j)
    def zeros(self,p):
        left=self.T*self.w;right=left+len(self.middle)
        def blankzeros(n):q,r=divmod(n,self.w);return q*self.zblank[-1]+self.zblank[r]
        if p<=left:return blankzeros(p)
        if p<=right:return blankzeros(left)+self.zmiddle[p-left]
        return blankzeros(left)+self.zmiddle[-1]+blankzeros(p-right)
    def init_bit(self,i):
        j=i-self.T*self.w
        return self.middle[j] if 0<=j<len(self.middle) else self.blank[i%self.w]
    def initial_prefix(self,p):return triangle(p)+5*p+self.zeros(p)
    def witness_prefix(self,p):return p*(self.G+3)+triangle(p)
    def length(self):return self.transition_prefix(self.T)+self.initial_prefix(self.R)+2+self.witness_prefix(self.C)+self.acceptance_prefix(self.C)+1
    def template_at(self,F,coord,t,j,k):
        for clause in F:
            c=tuple((coord(i,t,j),b) for i,b in clause);L=2+sum(v+3+int(not b) for v,b in c)
            if k<L:return clause_at(c,k)
            k-=L
        raise AssertionError('template length')
    def token(self,k):
        if not 0<=k<self.length():return None
        L=self.transition_prefix(self.T)
        if k<L:
            t,k=seek(self.T,self.transition_prefix,k);j,k=seek(self.J,lambda j:self.window_prefix(t,j),k)
            return self.template_at(self.trans,self.trans_coord,t,j,k)
        k-=L;L=self.initial_prefix(self.R)
        if k<L:
            i,k=seek(self.R,self.initial_prefix,k);return clause_at(((i,self.init_bit(i)),),k)
        k-=L;L=2+self.witness_prefix(self.C)
        if k<L:
            if k==0:return 6
            if k==L-1:return 3
            j,k=seek(self.C,self.witness_prefix,k-1);return literal_at(self.G+j,True,k)
        k-=L;L=self.acceptance_prefix(self.C)
        if k<L:
            j,k=seek(self.C,self.acceptance_prefix,k);return self.template_at(self.acc,self.acc_coord,0,j,k)
        assert k==L
        return 4
    def bit(self,i):
        if i<0:return None
        k,j=divmod(i,3);t=self.token(k);return None if t is None else (t>>(2-j))&1
