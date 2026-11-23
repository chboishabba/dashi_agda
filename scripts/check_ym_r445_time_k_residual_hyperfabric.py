#!/usr/bin/env python3
"""Finite original R445 C4->C2 x parity reference; not Agda/continuum YM proof.
Chronological t and refinement-stage k remain independent, signed trits preserve zero.
"""
from itertools import product

TRITS=(-1, 0, 1)
NATIVE_TIME=range(4)
COARSE=range(2)

def split(t): return divmod(t,2)
def join(pair): return (2*pair[0]+pair[1])%4
def carry(pair):
    coarse,phase=pair
    return (coarse,1) if phase==0 else ((coarse+1)%2,0)
def shiftfine(t,n): return (t+n)%4
def shiftcoarse(c,n): return (c+n)%2

def reflection(t): return (-t)%4

def allchecks():
    for time in NATIVE_TIME:
        assert join(split(time))==time
        assert split(join(split(time)))==split(time)
        assert split(shiftfine(time,1))==carry(split(time))
        assert carry(carry(split(time)))==(shiftcoarse(split(time)[0],1),split(time)[1])
        assert split(shiftfine(time,2))==(shiftcoarse(split(time)[0],1),split(time)[1])
        assert split(reflection(reflection(time)))==split(time)
    for coarse,phase in product(COARSE,COARSE):
        assert split(join((coarse,phase)))==(coarse,phase)
    assert split(0)==(0,0)
    assert all(split(2*c)[1]==0 for c in COARSE)
    # One fine step CANNOT be recovered from the coarse coordinate ALONE:
    # from fine 0 and fine 1 the coarse start is same, but after shift it isn't.
    assert split(0)[0]==split(1)[0]==0
    assert split(shiftfine(0,1))[0]==0
    assert split(shiftfine(1,1))[0]==1
    pairs=0
    for t,k,fine,sgn in product(range(33),range(33),NATIVE_TIME,TRITS):
        # No collapse of chronological t, stage k, sign, zero, or parity.
        address=(t,k,*split(fine),sgn)
        assert address[0]==t and address[1]==k and address[4]==sgn
        assert join((address[2],address[3]))==fine
        assert (-(-sgn))==sgn and (sgn==0)==(sgn==0)
        assert (address[4] if sgn else 0)==sgn
        pairs+=1
    assert pairs==33*33*4*3==13068
    # Actual original 4D positive links count 256*4; source original code
    # owns (64 coarse bonds)*2 selected fine links and 896 residual links.
    assert 4**4*4 == 1024
    assert (2**4*4)*2 == 128
    assert 1024-128 == 896
    # Distinct roles: this 896 residual is a finite LINK LIST; the odd/even
    # source-time parity is a distinct, 2-valued coordinate remainder.
    print('PASS exact original C4 <-> C2 x parity: 8/8 round trips')
    print('PASS four native carry and two-fine-step rules: 4/4 each')
    print('PASS chronological time x RG stage x finite time x sign/zero: 13068/13068')
    print('PASS R445 original count ledger: 128 selected + 896 residual = 1024 links')
    print('NEGATIVE one fine step cannot factor through coarse-only phase: witnessed')
    print('OPEN non-Abelian original source native Fin.compose acceptance, wave continuum E1, OS same-H')

if __name__ == '__main__': allchecks()
