"""Monotone blank-suffix contraction on the actual parsed candidate.
The written tape is a residual word (prefix, repeated cycle, suffix).
The raw run count is not the cost of computing this description.
"""
from itertools import product
from check_pnp_stack_fractran import compile_candidate_bits
from check_pnp_candidate_literal_endpoint import candidate_bits
from check_pnp_stack_priority_transport import AuditedRunner


def sweep(M,q,T):
    if T<0:raise ValueError('horizon')
    seen={};writes=[];states=[q]
    while len(writes)<T:
        if q in seen:
            a=seen[q];p=len(writes)-a;k,r=divmod(T-a,p)
            return tuple(writes[:a]),tuple(writes[a:]),k,tuple(writes[a:a+r]),states[a+r]
        seen[q]=len(writes)
        rule=next((z for z in M.rules if z[:2]==(q,M.blank)),None)
        if rule is None or rule[4]!=1:return None
        _,_,q,b,_=rule;writes.append(M.digit(b));states.append(q)
    return tuple(writes),(),0,(),q


def endpoint(M,q,L,llen,rlen,T,bit_cap=8192):
    """Input right value zero, scratch zero, valid extents; output symbolic.
    Materialize only when bounded. If all written digits and initial left
    value vanish, literal exponent and raw count remain compact.
    """
    if min(L,llen,T,bit_cap)<0 or rlen<1:raise ValueError('state')
    z=sweep(M,q,T)
    if z is None:return None
    pre,cycle,k,tail,p=z
    assert len(pre)+len(cycle)*k+len(tail)==T
    result=dict(q=p,word=z[:4],left_initial=L,llen=llen+T,rlen=max(1,rlen-T),right=0)
    if L==0 and not any(pre+cycle+tail):
        result.update(left=0,raw=6*T+min(T,rlen-1));return result
    if L.bit_length()+T*M.base.bit_length()+T.bit_length()+8>bit_cap:return result
    x=L;raw=0
    for j,b in enumerate(pre+cycle*k+tail):
        raw+=6+2*(1+M.base)*x+int(j<rlen-1);x=M.base*x+b
    result.update(left=x,raw=raw);return result


def main():
    count=huge=0
    for blank,b,c in product(range(2),repeat=3):
        rules=((0,blank,1,b,1),(0,blank,0,1-b,-1),(1,blank,0,c,1))
        M,_,_=compile_candidate_bits(2,2,len(rules),candidate_bits(2,2,blank,0,1,rules))
        A=AuditedRunner(M)
        for left,rlen in product(((),(blank,),(1-blank,)),range(1,4)):
            start=M.encode(0,left,(blank,)*rlen);v=start;raw=0
            for T in range(13):
                z=endpoint(M,0,start[0],start[3],rlen,T)
                assert (z['left'],0,0,z['llen'],z['rlen'])==v[:5]
                assert M.decode(v)[0]==z['q'] and z['raw']==raw
                count+=1
                v,h,cost=A.exact(v,True);assert not h;raw+=cost['raw']
        z=endpoint(M,0,0,0,1,10**60+1)
        assert z['q']==1 and z['llen']==10**60+1 and z['rlen']==1
        if b==c==blank:assert z['left']==0 and z['raw']==6*(10**60+1)
        else:assert 'left' not in z and 'raw' not in z
        huge+=1
    M,_,_=compile_candidate_bits(1,1,1,candidate_bits(1,1,0,0,0,((0,0,0,0,-1),)))
    assert endpoint(M,0,0,0,1,10) is None
    print(dict(finite=count,huge_symbolic=huge,reversal_refusal=1))
if __name__=='__main__':main()
