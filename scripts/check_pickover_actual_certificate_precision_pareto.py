#!/usr/bin/env python3
"""Measured small Pickover certificates; source Machin (1706); DASHI cost audit.
Exact integer enclosures. No claimed result at exponent 9999!.
"""
from math import factorial

def atan_fixed(S,d):
    j=0; p=d; sg=1; total=0
    while True:
        term=S//((2*j+1)*p)
        if not term: return total,j
        total+=sg*term
        sg=-sg
        j+=1
        p*=d*d

def pi_window(decimals):
    S=10**decimals
    a,na=atan_fixed(S,5)
    b,nb=atan_fixed(S,239)
    # Error from truncating individual terms and the alternating tail:
    # each division contributes less than one integer unit.
    err=16*(na+2)+4*(nb+2)
    lo=16*a-4*b-err
    hi=16*a-4*b+err
    assert 0<lo<hi
    return S,lo,hi,na,nb

def receipt(base,exponent,decimals):
    S,L,U,na,nb=pi_window(decimals)
    N=pow(base,exponent)
    qlo=N*S//U
    qhi=N*S//L
    if qlo!=qhi:
        return None
    return (1 if qlo%2==0 else -1,qlo,na+nb)

def main():
    rows=[]
    for base in (10,99):
        for n in (1,2,3,4,5):
            E=factorial(n)
            result=None
            for digits in range(10,400):
                r=receipt(base,E,digits)
                if r:
                    result=(digits,r)
                    break
            assert result is not None
            digits,(sign,q,terms)=result
            assert receipt(base,E,digits+10)[0]==sign
            rows.append((base,n,E,digits,terms,sign))
            print('base,n,E,digits,atan-terms,sign',*rows[-1])
    assert len(rows)==10
    print('PASS: 10 certified actual sine signs and first-successful precision')
    print('LIMIT: small instances, no Pickover terminal sign or sublinear phase algorithm')

if __name__=='__main__':
    main()
