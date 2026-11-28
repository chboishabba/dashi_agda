"""Attach paid row receipts to the original forced-pin route."""
from itertools import product
from random import Random
from check_pnp_affine_pin_dispatch import solve_pins
from check_pnp_rref_certificate import verify
from check_pnp_source_derived_cover import Reservation

def main():
    rng=Random(36928);cases=certs=0
    for n in range(1,8):
        for _ in range(24):
            A=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(rng.randrange(1,n+1)))
            t=tuple(rng.randrange(3) for _ in A)
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))) for _ in range(3))
            receipts=[];q=solve_pins(F,n,A,t,10**7,certificates=receipts)
            W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in A)==t]
            assert q['status']==('WITNESS' if W else 'EMPTY')
            if W:assert q['witness'] in W
            for z in receipts:assert verify(z['original'],len(z['coordinates']),z['receipt'],Reservation(10**7))
            cases+=1;certs+=len(receipts)
    print(dict(cases=cases,row_receipts=certs))
if __name__=='__main__':main()
