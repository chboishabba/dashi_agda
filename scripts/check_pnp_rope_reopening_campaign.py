"""Independent mixed block and actual parsed source-step reopening checks."""
from random import Random
from check_pnp_reentrant_sweep import block,pop,push,drop,at,length,expand,step,materialize
from check_pnp_stack_fractran import compile_candidate_bits,source_next
from check_pnp_candidate_literal_endpoint import candidate_bits

def main():
    rng=Random(3692801);descriptors=steps=0
    def rope(A):return tuple(z for _ in range(rng.randrange(6)) for z in block(tuple(rng.randrange(A) for _ in range(rng.randrange(5))),rng.randrange(5)))
    for _ in range(512):
        W=rope(3);X=tuple(a for w,k in W for a in w*k);assert length(W)==len(X) and expand(W,1000)==X
        b,V=pop(W,0);assert b==(X[0] if X else 0) and expand(V,1000)==X[1:]
        n=rng.randrange(len(X)+2);assert expand(drop(W,n),1000)==X[n:]
        b=rng.randrange(3);assert expand(push(W,b),1000)==(b,)+X
        if X:i=rng.randrange(len(X));assert at(W,i)==X[i]
        descriptors+=1
    for A in range(1,4):
        for blank in range(A):
            for _ in range(12):
                rules=tuple((q,a,rng.randrange(2),rng.randrange(A),rng.randrange(-1,2)) for q in range(2) for a in range(A))
                M,_,_=compile_candidate_bits(2,A,len(rules),candidate_bits(2,A,blank,0,1,rules))
                L,R=rope(A),rope(A) or block((blank,));s=(0,L,R);x=materialize(s,1000)
                for _ in range(20):
                    x=source_next(M,x);s=step(M,s);assert x==materialize(s,1000);steps+=1
    print(dict(descriptors=descriptors,source_steps=steps))
if __name__=='__main__':main()
