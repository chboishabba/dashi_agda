"""Exact packed endpoint and raw edge count for the original five-lane ABI.
Default campaign is independent arithmetic/word reference; --emitter uses
the actual existing compiler and priority runner, not a replacement emitter.
"""
from itertools import product
from collections import Counter
import sys

def pack(B,word):
    v=0
    for a in reversed(word):v=B*v+a
    return v

def formula(B,L,R,ll,rr,rule):
    d=R%B;t=R//B
    if rule is None:b=d;move=0
    else:b,move=rule
    common=lambda s:5+4*t+2*(1+B)*s
    if move==0:return (L,B*t+b,0,ll,rr),common(t),5
    if move==1:return (B*L+b,t,0,ll+1,max(1,rr-1)),common(L)+(2 if rr>=2 else 1),7 if rr>=2 else 6
    w=B*t+b
    return (L//B,B*w+L%B,0,max(0,ll-1),rr+1),common(t)+5+2*(1+B)*w+4*(L//B),10

def phase_reference(B,L,R,ll,rr,rule):
    v=[L,R,0,ll,rr];cost=phases=0
    def exit(take=None,give=None):
        nonlocal cost,phases
        if take is not None:
            i,a=take;assert v[i]>=a;v[i]-=a
        if give is not None:
            i,b=give;v[i]+=b
        cost+=1;phases+=1
    def transfer(x,a,y,b,take=None,give=None):
        nonlocal cost
        k=v[x]//a;v[x]-=a*k;v[y]+=b*k;cost+=2*k
        exit(take,give)
    exit()
    d=v[1]%B
    transfer(1,B,2,1,take=(1,d))
    transfer(2,1,1,1)
    b,move=(d,0) if rule is None else rule
    stack=0 if move==1 else 1
    transfer(stack,1,2,B)
    transfer(2,1,stack,1,give=(stack,b))
    if move==1:
        if v[4]>=2:
            exit((4,2),(3,1));exit(give=(4,1))
        else:exit(give=(3,1))
    elif move==-1:
        transfer(1,1,2,B);transfer(2,1,1,1)
        e=v[0]%B
        transfer(0,B,2,1,take=(0,e),give=(1,e))
        transfer(2,1,0,1)
        exit((3,1) if v[3] else None,(4,1))
    return tuple(v),cost,phases

def source_word(left,right,rule):
    if rule is None:return left,right
    b,m=rule;tail=right[1:]
    if m==0:return left,(b,)+tail
    if m==1:return (b,)+left,tail or (0,)
    return left[1:],((left[0] if left else 0),b)+tail

def main():
    C=Counter()
    for A in range(1,5):
        B=max(2,A)
        left=tuple(x for k in range(3) for x in product(range(A),repeat=k))
        right=tuple(x for k in range(1,4) for x in product(range(A),repeat=k))
        rules=(None,)+tuple(product(range(A),(-1,0,1)))
        for L,R,r in product(left,right,rules):
            p=(B,pack(B,L),pack(B,R),len(L),len(R),r)
            got=formula(*p);assert got==phase_reference(*p)
            u,v=source_word(L,R,r)
            assert got[0]==(pack(B,u),pack(B,v),0,len(u),len(v))
            assert got[2]<=10
            C['packed_word_endpoints']+=1
    print(dict(C))

def emitter():
    from check_pnp_stack_fractran import compile_stack, source_next
    from check_pnp_stack_priority_transport import AuditedRunner
    C=Counter()
    for A in range(1,4):
        for blank in range(A):
            for write,m in product(range(A),(-1,0,1)):
                # Distinct duplicate successor deliberately lower priority.
                rules=((0,0,1,write,m),(0,0,0,blank,0))
                M=compile_stack(2,A,blank,rules);runner=AuditedRunner(M)
                for q,L,R in product(range(2),((),(blank,),(0,blank)),((0,),(blank,),(0,blank))):
                    s=M.encode(q,L,R);a=M.symbol(s[1]%M.base)
                    rule=next(((M.digit(b),d) for p,z,t,b,d in rules if (p,z)==(q,a)),None)
                    got=formula(M.base,s[0],s[1],s[3],s[4],rule)
                    v,h,ledger=runner.exact(s,True)
                    w,j,raw=runner.exact(s,False)
                    assert (v,h)==(w,j) and ledger['raw']==raw['raw']==got[1]
                    assert v[:5]==got[0]
                    expected=source_next(M,(q,L,R))
                    assert M.decode(v)==((*expected,False) if expected is not None else (q,L,R,True))
                    C['actual_emitted_endpoints']+=1
    print(dict(C))

if __name__=='__main__':
    main()
    if '--emitter' in sys.argv:emitter()
