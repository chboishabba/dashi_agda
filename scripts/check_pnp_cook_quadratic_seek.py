"""Direct quadratic inverse for the original Cook seek layout.
Fixed templates, compact arithmetic model; not a same-target tape clock.
"""
from check_pnp_cook_affine_seek import CookSeek

def digit_sqrt(x):
    if x<0:raise ValueError('radicand')
    q=r=0
    for j in range((x.bit_length()+1)//2-1,-1,-1):
        r=(r<<2)|((x>>(2*j))&3);d=(q<<2)|1
        if r>=d:r-=d;q=(q<<1)|1
        else:q<<=1
    assert q*q<=x<(q+1)*(q+1)
    return q

def prefix(a,c,j):return a*j*(j-1)//2+c*j

def inverse(a,c,k):
    """Largest j>=0 with P(j)<=k; c>0, a>=0."""
    if a<0 or c<=0 or k<0:raise ValueError('prefix')
    if not a:return k//c
    b=2*c-a;d=digit_sqrt(b*b+8*a*k)
    j=(d-b)//(2*a)
    assert j>=0 and prefix(a,c,j)<=k<prefix(a,c,j+1)
    return j

def seek_quadratic(count,a,c,k):
    j=inverse(a,c,k);assert j<count
    return j,k-prefix(a,c,j)

class QuadraticCookSeek(CookSeek):
    def token(self,k):
        if not 0<=k<self.length():return None
        L=self.transition_prefix(self.T)
        if k<L:
            t,k=seek_quadratic(self.T,self.J*self.ta,self.window_prefix(0,self.J),k)
            j,k=seek_quadratic(self.J,self.tb,self.ta*t+self.tc,k)
            return self.template_at(self.trans,self.trans_coord,t,j,k)
        k-=L;L=self.initial_prefix(self.R)
        if k<L:
            # Actual zero count is between 0 and p. P6(p-1)<P5(p),
            # so the true index differs from the P5 inverse by at most one.
            p=inverse(1,5,k)
            if self.initial_prefix(p)>k:p-=1
            assert 0<=p<self.R and self.initial_prefix(p)<=k<self.initial_prefix(p+1)
            from check_pnp_cook_affine_seek import clause_at
            return clause_at(((p,self.init_bit(p)),),k-self.initial_prefix(p))
        k-=L;L=2+self.witness_prefix(self.C)
        if k<L:
            if k==0:return 6
            if k==L-1:return 3
            from check_pnp_cook_affine_seek import literal_at
            j,k=seek_quadratic(self.C,1,self.G+3,k-1)
            return literal_at(self.G+j,True,k)
        k-=L;L=self.acceptance_prefix(self.C)
        if k<L:
            j,k=seek_quadratic(self.C,self.ab,self.ac,k)
            return self.template_at(self.acc,self.acc_coord,0,j,k)
        assert k==L
        return 4
