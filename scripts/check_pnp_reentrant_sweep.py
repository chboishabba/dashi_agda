"""Reopen actual source tape after a symbolic right-only blank sweep.
A rope stores top-first repeated finite blocks, with exact extents.
No claim of cheap materialized FRACTRAN integer or same-target clock.
"""
from check_pnp_blank_sweep import sweep
from check_pnp_stack_fractran import compile_candidate_bits,source_next
from check_pnp_candidate_literal_endpoint import candidate_bits
from check_pnp_stack_priority_transport import AuditedRunner
from itertools import product


def block(w,k=1):
    w=tuple(w)
    return ((w,k),) if w and k else ()


def length(W):return sum(len(w)*k for w,k in W)


def pop(W,blank):
    if not W:return blank,()
    (w,k),*tail=W
    return w[0],block(w[1:])+block(w,k-1)+tuple(tail)


def push(W,b):return block((b,))+W


def at(W,i):
    if not 0<=i<length(W):raise IndexError(i)
    for w,k in W:
        if i<len(w)*k:return w[i%len(w)]
        i-=len(w)*k
    raise AssertionError('extent')


def expand(W,cap):
    if length(W)>cap:return None
    return tuple(b for w,k in W for b in w*k)


def drop(W,n):
    if n<0:raise ValueError('drop')
    for j,(w,k) in enumerate(W):
        count=len(w)*k
        if n>=count:n-=count;continue
        q,r=divmod(n,len(w))
        return (block(w[r:])+block(w,k-q-1) if r else block(w,k-q))+W[j+1:]
    return ()


def blank_prefix(W,blank,T):
    left=T
    for w,k in W:
        if not left:return True
        m=min(left,len(w)*k)
        if any(b!=blank for b in w[:min(m,len(w))]):return False
        left-=m
    return True # implicit cells past the explicit right extent are blank


def reopen_suffix(M,q,L,R,T):
    if not R or not blank_prefix(R,M.blank,T):raise ValueError('blank suffix')
    z=sweep(M,q,T)
    if z is None:return None
    pre,cycle,k,tail,p=z
    dec=lambda w:tuple(M.symbol(b) for b in reversed(w))
    left=block(dec(tail))+block(dec(cycle),k)+block(dec(pre))+L
    right=drop(R,T) or block((M.blank,))
    assert length(left)==length(L)+T
    return p,left,right


def reopen(M,q,L,R,T):return reopen_suffix(M,q,block(L),block(R),T)


def step(M,s):
    q,L,R=s;a,tail=pop(R,M.blank)
    r=next((z for z in M.rules if z[:2]==(q,a)),None)
    if r is None:return None
    _,_,p,b,d=r
    if d==1:return p,push(L,b),tail or block((M.blank,))
    if d==0:return p,L,push(tail,b)
    c,left=pop(L,M.blank)
    return p,left,push(push(tail,b),c)


def materialize(s,cap):
    q,L,R=s
    if length(L)+length(R)>cap:return None
    return q,expand(L,cap),expand(R,cap)


def main():
    finite=huge=0
    # Actual reversal occurs when the right-moving blank loop reaches
    # the original nonblank sentinel, not by changing control externally.
    for blank in range(2):
        non=1-blank
        rules=((0,blank,0,non,1),(0,non,1,blank,-1),(1,blank,1,non,-1),(1,non,1,blank,-1))
        M,_,_=compile_candidate_bits(2,2,len(rules),candidate_bits(2,2,blank,0,1,rules))
        A=AuditedRunner(M)
        for L,tail,T in product(((),(blank,),(non,blank)),((),(blank,)),range(10)):
            R=(blank,)*T+(non,)+tail
            s=reopen(M,0,L,R,T);v=M.encode(0,L,R)
            for _ in range(T):v,h,c=A.exact(v,True);assert not h
            assert materialize(s,100)==M.decode(v)[:3]
            for _ in range(6):
                s=step(M,s);v,h,c=A.exact(v,True);assert not h
                assert materialize(s,100)==M.decode(v)[:3];finite+=1
        T=10**60+1;R=block((blank,),T)+block((non,));s=reopen_suffix(M,0,block((blank,)),R,T)
        assert length(s[1])==T+1 and at(s[1],0)==non and at(s[1],T-1)==non and at(s[1],T)==blank
        assert at(s[2],0)==non and materialize(s,100) is None
        for j in range(32):
            s=step(M,s);assert s[0]==1 and length(s[1])==T-j and at(s[2],0)==non
            huge+=1
        try:reopen_suffix(M,0,(),R,T+1);raise AssertionError('sentinel erased')
        except ValueError:pass
    print(dict(finite_reverse_endpoints=finite,huge_reverse_steps=huge))
if __name__=='__main__':main()
