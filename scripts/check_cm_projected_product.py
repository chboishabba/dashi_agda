"""Exact consumer-selected nonnegative Kronecker product."""
def selected_product(a,b,n,p,r):
    if p<1 or n<0 or r<2 or not a or not b:
        raise ValueError('invalid carrier')
    a=[x%r for x in a[:n+1]]; b=[x%r for x in b[:n+1]]
    bound=min(len(a),len(b))*max(a)*max(b)
    w=max(1,(bound.bit_length()+7)//8)
    A=int.from_bytes(b''.join(x.to_bytes(w,'little') for x in a),'little')
    B=int.from_bytes(b''.join(x.to_bytes(w,'little') for x in b),'little')
    C=A*B
    raw=C.to_bytes(max((n+1)*w,(C.bit_length()+7)//8),'little')
    return [int.from_bytes(raw[k*w:(k+1)*w],'little')%r for k in range(0,n+1,p)]

def complementary_product(a,b,n,p,r,mul):
    out=mul(a[::p],b[::p],n,r)
    for i in range(1,p):
        if n and a[i::p] and b[p-i::p]:
            v=mul(a[i::p],b[p-i::p],n-1,r)
            for j,x in enumerate(v):out[j+1]=(out[j+1]+x)%r
    return out

def main():
    from random import Random
    from sympy import Poly, symbols, ZZ
    x=symbols('x'); rng=Random(9); count=0
    for p in (3,5,7,11,17,41):
        for n in (1,2,3):
            for r in (83,83**2,739**3,2**384):
                a=[rng.randrange(-r,r) for _ in range(p*n+1)]
                b=[rng.randrange(-r,r) for _ in a]
                def mul(a,b,n,r):
                    c=[0]*(n+1)
                    for i,u in enumerate(a[:n+1]):
                        for j,v in enumerate(b[:n+1-i]):c[i+j]=(c[i+j]+u*v)%r
                    return c
                z=Poly.from_list(a[::-1],x,domain=ZZ)*Poly.from_list(b[::-1],x,domain=ZZ)
                ref=[int(z.nth(k*p))%r for k in range(n+1)]
                assert selected_product(a,b,p*n,p,r)==ref==complementary_product(a,b,n,p,r,mul)
                count+=1
    print('PASS',count,'three-way SymPy/projected/complementary cases')

if __name__=='__main__':main()
