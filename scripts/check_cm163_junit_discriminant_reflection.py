#!/usr/bin/env python3
"""Exact alternative J=q*j coefficient source, not a second analytic j.
The original E4/E6 divisor streams and Delta=(E4^3-E6^2)/1728
imply U=Delta/q with U[0]=1. Reflect J*U=E4^3 by triangular
integer recurrence, and compare to the original eta-based producer.
This is finite arithmetic, not formal analytic reflection.
"""
import hashlib
from pathlib import Path
from time import perf_counter
from check_cm163_modular_diagonal import j_unit, convolution

PINNED = 'add8e35866aa1e9f379b4a57059c4487e4c7241c'

def require(ok, msg):
    if not ok:
        raise AssertionError(msg)

def verify_source():
    b = Path(__file__).with_name('check_cm163_modular_diagonal.py').read_bytes()
    require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==PINNED,
            'changed original source')

def from_discriminant(M):
    n=M+1
    s3=[0]*(n+1);s5=[0]*(n+1)
    for d in range(1,n+1):
        d3=d**3;d5=d**5
        for k in range(d,n+1,d):
            s3[k]+=d3;s5[k]+=d5
    e4=[1]+[240*x for x in s3[1:]]
    e6=[1]+[-504*x for x in s5[1:]]
    a=convolution(convolution(e4,e4,n),e4,n)
    b=convolution(e6,e6,n)
    require(a[0]==b[0]==1,'zero discriminant mode')
    U=[]
    for k in range(1,n+1):
        c,r=divmod(a[k]-b[k],1728)
        require(r==0,'nonintegral Delta coefficient at '+str(k))
        U.append(c)
    require(U[0]==1,'nonunit Delta/q')
    J=[a[0]]
    for k in range(1,M+1):
        J.append(a[k]-sum(U[i]*J[k-i] for i in range(1,k+1)))
    return J

def main():
    verify_source()
    M=41*82
    start=perf_counter()
    actual=from_discriminant(M)
    print('discriminant recurrence complete',flush=True)
    original=j_unit(M)
    for k,(a,b) in enumerate(zip(actual,original,strict=True)):
        require(a==b,'J discrepancy at '+str(k))
    require(len(actual)==M+1,'frontier length')
    print(f'PASS {M+1}/{M+1} exact J coefficients through degree {M}',flush=True)
    print('elapsed seconds',perf_counter()-start,flush=True)

if __name__=='__main__':
    main()
