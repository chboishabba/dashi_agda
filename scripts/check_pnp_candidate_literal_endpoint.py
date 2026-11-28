"""Attach original candidate-bit parsing to literal ordered FRACTRAN receipt.
No virtual-to-physical clock identification or unrestricted claim.
"""
from itertools import product
from check_pnp_stack_fractran import compile_candidate_bits, compile_stack, source_next
from check_pnp_hyperfabric_owned_joins import literal_instruction, alloc_lane_prime
from check_pnp_stack_priority_transport import AuditedRunner

def candidate_bits(q,a,blank,initial,accept,rules):
    one=lambda n,j:tuple(int(k==j) for k in range(n))
    return one(a,blank)+one(q,initial)+one(q,accept)+tuple(
        v for x,y,z,w,d in rules
        for v in one(q,x)+one(a,y)+one(q,z)+one(a,w)+one(3,d+1))

def main():
    count=0
    for blank,write,direction in product(range(2),range(2),(-1,0,1)):
        # Duplicate source rules must retain FIRST source transition.
        rules=((0,0,1,write,direction),(0,0,0,1-write,-direction),
               (1,1,0,blank,0))
        bits=candidate_bits(2,2,blank,0,1,rules)
        M,initial,accept=compile_candidate_bits(2,2,len(rules),bits)
        direct=compile_stack(2,2,blank,rules)
        assert (M.tags,M.sparse,initial,accept)==(direct.tags,direct.sparse,0,1)
        assert len(alloc_lane_prime(M))==len(M.tags)
        R=AuditedRunner(M)
        for q,L,V in product(range(2),((),(blank,),(1-blank,)),((0,),(1,),(blank,0))):
            s=M.encode(q,L,V);want=source_next(M,(q,L,V))
            result=literal_instruction(M,s,100000,10000)
            assert result is not None
            u,h,k=result
            w,j,ledger=R.exact(s,True)
            assert (u,h,k)==(w,j,ledger["raw"])
            assert M.decode(u)==(*(want if want is not None else (q,L,V)),want is None)
            count+=1
    print(dict(candidate_literal_endpoint=count))
if __name__=="__main__":main()
