#!/usr/bin/env python3
"""Exact replay of original unit, diagonal, slice and cusp-window predicates.
Use --packet for direct literal comparison, otherwise report digest-only.
Not analytic or kernel acceptance. Each stage can run under timeout 90s.
"""
import argparse, ctypes, hashlib, json, subprocess, tempfile
from fractions import Fraction as F
from pathlib import Path
from time import monotonic
import check_paper9_full_hecke_symmetry as O
from check_paper9_signed_integer_matrix_weld import signed_conv as conv, inverse

def units():
    d=3322; m=d+1
    s3=[0]*(m+1); s5=s3.copy()
    for k in range(1,m+1):
        for n in range(k,m+1,k):
            s3[n]+=k**3; s5[n]+=k**5
    e4=[1]+[240*x for x in s3[1:]]
    e6=[1]+[-504*x for x in s5[1:]]
    a=O.conv(O.conv(e4,e4,m),e4,m); b=conv(e6,e6,m)
    u=[]
    for n in range(d+1):
        q,r=divmod(a[n+1]-b[n+1],1728)
        assert r==0; u.append(q)
    j=O.junit(d)
    assert u[0]==j[0]==1 and conv(u,j,d)==a[:d+1]
    return j,2*(d+1)

def sector(j,c,diag):
    d=82 if diag else 42; m=41*d; K=-640320**3
    def at(n): return j[n] if 0<=n<len(j) else 0
    def ram(n): return at(n//41) if n%41==0 else 0
    h=[ram(n)-at(n-40) if diag else at(n)-(K if n==1 else 0) for n in range(m+1)]
    g=[at(n-40)-ram(n) if diag else ram(n)-(K if n==41 else 0) for n in range(d+1)]
    dh=[n*x for n,x in enumerate(h)]
    l=conv(dh,inverse(h,m),m)
    assert h[0]==1 and l[0]==0 and conv(h,l,m)==dh
    v=l[::41]; N=[1]
    for n in range(1,d+1):
        q,r=divmod(sum(v[i]*N[n-i] for i in range(1,n+1)),n)
        assert r==0; N.append(q)
    assert conv(N,v,d)==[n*x for n,x in enumerate(N)]
    col=[c[0]]+[0]*d
    for k in range(1,d+1):
        col=conv(j[:d+1],col,d); col[k]+=c[k]
    assert conv(g,N,d)==col
    return m+1+2*(d+1)

def windows():
    def atan(d,n): return sum((F((-1)**k,(2*k+1)*d**(2*k+1)) for k in range(n)),F(0))
    scale=2**128
    pl,ph=1069028584064966747859680373161870783300,1069028584064966747859680373161870783301
    sl,sh=4344434433350621975299947493401713860084,4344434433350621975299947493401713860085
    assert F(pl,scale)<=16*atan(5,90)-4*atan(239,31)
    assert 16*atan(5,91)-4*atan(239,30)<=F(ph,scale)
    assert sl**2<=163*scale**2<=sh**2
    lo,hi=F(pl*sl,scale**2),F(ph*sh,scale**2)
    assert 0<=lo<=hi and 2*hi<181
    def exp(x):
        t=F(1); a=t
        for n in range(1,180): t=t*x/n; a+=t
        return a,t*x/180
    l,_=exp(lo); u,tail=exp(hi); K=640320**3+744
    assert K-F(1,4)<l and u+2*tail<K+F(1,4)
    return {'piRoundOK':True,'sqrtRoundOK':True,'expWindowOK':True}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--packet',type=Path)
    ap.add_argument('--stage',choices=['unit','diagonal','slice','windows','all'],default='all')
    args=ap.parse_args(); start=monotonic(); out={}
    if args.stage in ('all','windows'):
        out.update(windows()); print('PASS windows',out,flush=True)
    if args.stage!='windows':
        with tempfile.TemporaryDirectory() as tmp:
            lib=Path(tmp)/'mul.so'
            subprocess.run(['g++','-O3','-shared','-fPIC',str(Path(__file__).with_name('paper9_hecke_packed_mul.cpp')),'-lgmp','-o',str(lib)],check=True)
            dll=ctypes.CDLL(str(lib)); O._mul=dll.multiply
            O._mul.argtypes=[ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t,ctypes.c_void_p,ctypes.c_size_t]; O._mul.restype=None
            j,count=units(); out['unitOK']=count; print('PASS unit',count,flush=True)
            if args.stage in ('all','diagonal','slice'):
                _,diag,fixed,_=O.matrix(); assert diag[-2:]==[0,0]
                d,c=diag[:-2][::-1],fixed[::-1]
                if args.packet:
                    pd,pc,blob=O.original_packet(args.packet); assert d==pd and c==pc; out['literal_packet_blob']=blob
                else:
                    digest=lambda a:hashlib.sha256(','.join(map(str,a)).encode()).hexdigest()
                    assert digest(d)=='85132a72355a35b15add35de7941526ef7800f3fdb3daf22559b354343f263f9'
                    assert digest(c)=='3391a057a0fe7f6f6ff9151e6fbc5e826d7e3be89776145c2e58d21857b4ea96'
                    out['literal_packet_comparison']='historical digest only'
                for name,cs,flag in [('diagonal',d,True),('slice',c,False)]:
                    if args.stage in ('all',name):
                        out[name+'OK']=sector(j,cs,flag); print('PASS',name,out[name+'OK'],flush=True)
    print(json.dumps({'results':out,'seconds':monotonic()-start},sort_keys=True),flush=True)

if __name__=='__main__': main()
