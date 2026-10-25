#!/usr/bin/env python3
"""Exact 2x punctured-nine / hexadecimal carry codec and equivariance no-go.
Classic Z/16 operations; DASHI source-specific punctured nine constructors.
No claimed sine-sign oracle or BBP acceleration.
"""
from math import factorial
P=('negativeFirstAxis','positiveFirstAxis','negativeSecondAxis',
   'positiveSecondAxis','negativeEqualDiagonal','positiveEqualDiagonal',
   'negativeOppositeDiagonal','positiveOppositeDiagonal')
ANTIPODE=(1,0,3,2,5,4,7,6)
def encode(sheet,point): return 8*sheet+point
def decode(n):
    assert 0<=n<16
    return divmod(n,8)
def add_carry(x,y):
    a,b=decode(x);c,d=decode(y)
    lo=b+d
    return ((a+c+lo//8)%2,lo%8)
def main():
    assert len(set(P))==8
    for i in range(16):
        assert encode(*decode(i))==i
        for j in range(16):
            assert encode(*add_carry(i,j))==(i+j)%16
            assert encode(*add_carry(j,i))==encode(*add_carry(i,j))
    for i in range(8):
        assert ANTIPODE[ANTIPODE[i]]==i and ANTIPODE[i]!=i
    native_fixed=sum(ANTIPODE[i]==i for sheet in range(2) for i in range(8))
    hex_fixed=[i for i in range(16) if (-i)%16==i]
    assert native_fixed==0 and hex_fixed==[0,8]
    print('PASS: sixteen structured labels, transported Z16 addition/carry')
    print('PASS: no equivariant bijection for native antipode vs Z16 negation (0 versus 2 fixed points)')
    for n in (5,7,10,100,9999):
        k=factorial(n)
        print('n',n,'bit_length',k.bit_length(),
              'squarings',k.bit_length()-1,'selected_multiplies',k.bit_count())
    assert factorial(9999).bit_length()==118445
    print('OPEN: no intrinsic ring morphism, BBP extraction speedup or real sine sign follows')
if __name__=='__main__':main()
