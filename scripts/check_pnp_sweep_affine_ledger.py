"""Exact affine sweep ledger, including symbolic modular huge raw counts.
The represented raw count is NOT host execution time or physical shortcut.
"""
from check_pnp_blank_sweep import sweep
from check_pnp_stack_fractran import compile_candidate_bits
from check_pnp_candidate_literal_endpoint import candidate_bits
from check_pnp_stack_priority_transport import AuditedRunner
from itertools import product

# L -> aL+b, cumulative sum of PRE-step L -> cL+d.
def compose(f,g,mod=None):
    a,b,c,d=f;e,h,i,j=g
    z=(e*a,e*b+h,c+i*a,d+i*b+j)
    return z if mod is None else tuple(x%mod for x in z)

def block(B,word,mod=None):
    z=(1,0,0,0)
    for b in word:z=compose(z,(B,b,1,0),mod)
    return z

def power(f,k,mod=None):
    if k<0:raise ValueError('repetitions')
    z=(1,0,0,0)
    while k:
        if k&1:z=compose(z,f,mod)
        k//=2
        if k:f=compose(f,f,mod)
    return z

def ledger(B,descriptor,L,rr,mod=None,bit_cap=4096):
    pre,cycle,k,tail,q=descriptor
    T=len(pre)+len(cycle)*k+len(tail)
    if mod is None and L==0 and not any(pre+cycle+tail):return 0,6*T+min(T,rr-1)
    if mod is None and L.bit_length()+T*B.bit_length()+2*T.bit_length()+16>bit_cap:return None
    a,b,c,d=compose(compose(block(B,pre,mod),power(block(B,cycle,mod),k,mod),mod),block(B,tail,mod),mod)
    z=(a*L+b,6*T+2*(1+B)*(c*L+d)+min(T,rr-1))
    return z if mod is None else tuple(v%mod for v in z)

def main():
    finite=huge=0
    for blank,b,c in product(range(2),repeat=3):
        rules=((0,blank,1,b,1),(1,blank,0,c,1))
        M,_,_=compile_candidate_bits(2,2,len(rules),candidate_bits(2,2,blank,0,1,rules));A=AuditedRunner(M)
        for left,rr in product(((),(blank,),(1-blank,)),range(1,4)):
            v=M.encode(0,left,(blank,)*rr);L=v[0];raw=0
            for T in range(13):
                z=sweep(M,0,T);assert ledger(M.base,z,L,rr)==(v[0],raw)
                for p in (3,5,43):assert ledger(M.base,z,L,rr,p)==(v[0]%p,raw%p)
                finite+=1
                v,h,cost=A.exact(v,True);assert not h;raw+=cost['raw']
        T=10**60+1;z=sweep(M,0,T)
        for p in (3,5,43,65537):
            # independent finite-state modular iteration with cycle skipping
            state=(0,0,0);seen={};j=0
            while j<T:
                if state in seen:
                    period=j-seen[state];skip=(T-j)//period
                    if skip:j+=skip*period;continue
                else:seen[state]=j
                q,L,s=state;digit=M.digit(b if q==0 else c);state=(1-q,(2*L+digit)%p,(s+L)%p);j+=1
                # keep reference state space small; large modulus uses finite composition checks instead
                if p>43 and j==100:break
            if j==T:assert ledger(2,z,0,1,p)==(state[1],(6*T+6*state[2])%p)
            else:
                a=ledger(2,sweep(M,0,100),0,1,p);assert a==(state[1],(600+6*state[2])%p)
            huge+=int(j==T)
        if b==c==blank:assert ledger(2,z,0,1)==(0,6*T)
        else:assert ledger(2,z,0,1) is None
    print(dict(finite=finite,huge_modular=huge))
if __name__=='__main__':main()
