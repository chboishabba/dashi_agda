#!/usr/bin/env python3
"""Exact full prime-41 polynomial from original J recurrence, no CM recognition.
Finite principal-part reflection only; analytic modular rigidity is separate.
"""
from math import comb
from time import monotonic
import ctypes
from pathlib import Path
import subprocess
import tempfile
import re
import hashlib
import sys

P = 41
D = P+1
K = -640320**3

def conv(a,b,n):
    # Exact Kronecker packing for nonnegative coefficient streams.
    if not any(a) or not any(b): return [0]*(n+1)
    assert min(a)>=0 and min(b)>=0
    w=(max(a).bit_length()+max(b).bit_length()+min(len(a),len(b)).bit_length()+7)//8
    aa=b''.join(x.to_bytes(w,'little') for x in a)
    bb=b''.join(x.to_bytes(w,'little') for x in b)
    out=ctypes.create_string_buffer(w*(n+1))
    _mul(aa,len(aa),bb,len(bb),out,len(out))
    cc=out.raw
    return [int.from_bytes(cc[i*w:(i+1)*w],'little') for i in range(n+1)]

def junit(n):
    s1=[0]*(n+1);s3=[0]*(n+1)
    for d in range(1,n+1):
        for k in range(d,n+1,d):
            s1[k]+=d;s3[k]+=d**3
    e=[1]+[240*x for x in s3[1:]]
    inv=[1]
    for k in range(1,n+1):
        a,b=divmod(sum(24*s1[i]*inv[k-i] for i in range(1,k+1)),k)
        assert not b;inv.append(a)
    return conv(conv(conv(e,e,n),e,n),inv,n)

def matrix():
    n=P*D
    J=junit(n)
    power=[1]; traces=[None]
    for k in range(1,P+1):
        power=conv(power,J,n)
        traces.append([P*power[P*i+k] for i in range(P+1)])
    # e_k, k<41, has no negative q mode. e_41 has q^-1=1.
    e=[[1]+[0]*P]
    divisions=0
    for k in range(1,P+1):
        row=[]
        for j in range(P+1):
            a,b=divmod(sum((-1)**(i-1)*sum(e[k-i][j-h]*traces[i][h] for h in range(j+1)) for i in range(1,k+1)),k)
            assert not b;row.append(a);divisions+=1
        e.append(row)
    assert e[0][0]==1
    # F=prod(Y-j(zeta^a t))*(Y-j(q^41)). F has pole at most q^-42.
    # Represent each Y column of q^42 F through q^42.
    cols=[[0]*(D+1) for _ in range(D+1)]
    for k in range(P+1):
        y=P-k; sign=(-1)**k
        cols[y+1][D]+=sign*e[k][0]
        for j in range(P+1): cols[y][1+j]-=sign*e[k][j]
        cols[y][D]-=744*sign*e[k][0]
        if k==P:
            cols[y+1][D-1]+=sign
            cols[y][0]-=sign
            cols[y][D-1]-=744*sign
    powers=[[1]+[0]*D]
    for k in range(D): powers.append(conv(powers[-1],J[:D+1],D))
    phi=[[0]*(D+1) for _ in range(D+1)]
    for y,col in enumerate(cols):
        rem=col[:]
        for x in range(D,-1,-1):
            c=rem[D-x];phi[x][y]=c
            for j in range(x+1): rem[D-x+j]-=c*powers[x][j]
        assert not any(rem)
    assert phi[D][0]==phi[0][D]==1
    assert all(phi[x][y]==phi[y][x] for x in range(D+1) for y in range(D+1))
    assert all(phi[D][y]==0 for y in range(1,D+1))
    diagonal=[sum(phi[x][d-x] for x in range(D+1) if 0<=d-x<=D) for d in range(2*D+1)]
    fixed=[sum(phi[x][y]*K**y for y in range(D+1)) for x in range(D+1)]
    # Signed centered coefficient ratios from original diagonal and slice.
    shift=lambda cs,k:sum(c*comb(i,k)*K**(i-k) for i,c in enumerate(cs) if i>=k)
    assert shift(diagonal,0)==shift(diagonal,1)==shift(fixed,0)==shift(fixed,1)==0
    p2,p3,s2,s3=shift(diagonal,2),shift(diagonal,3),shift(fixed,2),shift(fixed,3)
    assert s2!=0 and 41*p2==163*s2
    assert (41*p3-326*s3)*19943834790540897829879824384000==-77859659565707*163*s2
    return phi,diagonal,fixed,divisions

def original_packet(path):
    raw=path.read_bytes()
    source=raw.decode()
    def read(label, body):
        return [(-1 if m[0] else 1)*int(m[1]) for m in re.findall(r'(Z\.- )?\(?\+ (\d+)\)? / 1',body)]
    a,b=source.split('slice : List',1)
    diag=read('diagonal',a.split('diagonal =',1)[1])
    fixed=read('slice',b.split('slice =',1)[1])
    return diag,fixed,hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()

def main():
    global _mul
    root=Path(__file__).resolve().parent
    start=monotonic()
    with tempfile.TemporaryDirectory() as tmp:
        lib=Path(tmp)/'mul.so'
        subprocess.run(['g++','-O3','-shared','-fPIC',str(root/'paper9_hecke_packed_mul.cpp'),'-lgmp','-o',str(lib)],check=True)
        dll=ctypes.CDLL(str(lib))
        _mul=dll.multiply
        _mul.argtypes=[ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t,ctypes.c_void_p,ctypes.c_size_t]
        _mul.restype=None
        phi,diag,fixed,divisions=matrix()
        assert diag[-1]==diag[-2]==0
        a,b=diag[:-2][::-1],fixed[::-1]
        if '--digest-only' in sys.argv:
            digest=lambda cs:hashlib.sha256(','.join(map(str,cs)).encode()).hexdigest()
            assert digest(a)=='85132a72355a35b15add35de7941526ef7800f3fdb3daf22559b354343f263f9'
            assert digest(b)=='3391a057a0fe7f6f6ff9151e6fbc5e826d7e3be89776145c2e58d21857b4ea96'
            sha='digest-only: original packet blob eb41e2c937d89dfb8cf2f90d1f31e69b945ad5e0'
        else:
            originalD,originalS,sha=original_packet(root.parent/'DASHI/Moonshine/JInvariantBishopCM163LiteralPacketExact.agda')
            assert a==originalD and b==originalS
        print('PASS',divisions,'exact Newton divisions;',len(phi)**2,'symmetry entries;',len(a)+len(b),'literal packet coefficients (digest or direct); signed CM ratios',flush=True)
        print('literal blob',sha,'seconds',monotonic()-start,flush=True)

if __name__=='__main__':main()
