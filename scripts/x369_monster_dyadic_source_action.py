"""Exact dyadic Conway/Seysen weight-two action via bounded atom CRT.

Original sources (not DASHI inventions):
Conway 1985, A simple construction of the Fischer-Griess monster group.
Seysen 2020 arXiv:2002.10921v3, sections 7--9, especially 9.11,9.16.
https://mmgroup.readthedocs.io/en/latest/guide.html (triality formula).
The literal standard atoms d,p,x,y act monomially. t has the 3-entry
triality blocks and 64-entry 1/8 Hadamard blocks. l has 24x blocks with
1/2 entries, symmetric-square blocks, 4096x blocks with 1/4 entries,
and their tensor products with denominator 8; the short-vector part is
monomial. The public coordinate conventions retain these dyadic bounds.

Use a conservative denominator 16, entry bound 4 and at most 256
entries in each row/column, so a digit of maximum 127 yields scaled
integer bound 16*4*256*127 < half the CRT product. This is a
source-formula-dependent exact reconstruction, not an inference of
characteristic-zero equality from arbitrary modular residues.
Never treat an unsupported compressed atom or a whole long word as a
single bounded atom. No JMD u/v source or full FLM product is invented.
"""
from dataclasses import dataclass
from functools import reduce
from math import prod
from pathlib import Path
from time import monotonic
import argparse
import hashlib
import json
import numpy as np

DIM=196884
MODULI=(7,31,127,255)
MODULUS=prod(MODULI)
SCALE=16
ROW_L1_BOUND=SCALE*4*256
DIGIT_BASE=128
TAGS=('d','p','x','y','t','l')
CRT_FACTORS=tuple((MODULUS//p)*pow(MODULUS//p,-1,p) for p in MODULI)


def require(ok,msg):
    if not ok:raise ValueError(msg)


def centered_crt(residues,bound):
    require(0<=bound<MODULUS/2 and len(residues)==len(MODULI),'CRT uniqueness bound')
    a=sum(np.asarray(x,dtype=np.int64)*c for x,c in zip(residues,CRT_FACTORS))%MODULUS
    a=np.where(a>MODULUS//2,a-MODULUS,a)
    require(bool(np.all(np.abs(a)<=bound)),'source atom coefficient bound violated')
    return a


@dataclass
class Dyadic:
    numerator: object
    power: int=0

    def __post_init__(self):
        a=np.asarray(self.numerator,dtype=object)
        require(a.shape==(DIM,) and type(self.power) is int and self.power>=0 and
                all(type(x) is int for x in a),'exact dyadic vector')
        self.numerator=a
        self.normalise()

    def normalise(self):
        while self.power and not np.any(self.numerator%2):
            self.numerator=self.numerator//2;self.power-=1

    def residue(self,p):
        return np.asarray((self.numerator%p)*pow(pow(2,self.power,p),-1,p)%p,dtype=np.uint8)

    def same(self,other):
        return self.power==other.power and np.array_equal(self.numerator,other.numerator)

    def sparse(self):
        from fractions import Fraction
        d=1<<self.power
        return {str(int(i)):[str(Fraction(self.numerator[i],d)),'0']
                for i in np.flatnonzero(self.numerator)}

    def digest(self):
        return hashlib.sha256(json.dumps(self.sparse(),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def unit(i):
    require(type(i) is int and 0<=i<DIM,'actual V2 basis column')
    a=np.zeros(DIM,dtype=object);a[i]=1
    return Dyadic(a)


def atoms(g):
    from mmgroup import MM
    rows=g.as_tuples()
    require(all(len(a)==2 and a[0] in TAGS for a in rows),'unsupported nonprimitive source atom')
    require(MM(rows)==g,'literal source word reconstruction')
    return rows


def atom_action(v,atom):
    from mmgroup import MM,MMV
    require(len(atom)==2 and atom[0] in TAGS,'primitive standard atom only')
    g=MM(*atom)
    a=v.numerator
    out=np.zeros(DIM,dtype=object)
    sign=np.where(a<0,-1,1);mag=np.abs(a);place=1
    while np.any(mag):
        digits=(mag%DIGIT_BASE)*sign;mag=mag//DIGIT_BASE
        bound=int(np.max(np.abs(digits)))*ROW_L1_BOUND
        if bound:
            residues=[]
            for p in MODULI:
                vec=MMV(p)('V',np.asarray(digits%p,dtype=np.uint8))
                r=np.asarray((vec*g)['E'],dtype=np.int64)
                require(r.shape==(DIM,),'actual source representation')
                residues.append(r*SCALE%p)
            lift=centered_crt(residues,bound)
            out+=lift.astype(object)*place
        place*=DIGIT_BASE
    return Dyadic(out,v.power+4)


def action(v,g,deadline=None):
    for a in atoms(g):
        if deadline is not None and monotonic()>=deadline:raise TimeoutError('source atom budget')
        v=atom_action(v,a)
    return v


def verify(v,w,g):
    from mmgroup import MMV
    for p in MODULI:
        source=MMV(p)('V',v.residue(p))*g
        require(np.array_equal(np.asarray(source['E'],dtype=np.uint8)%p,w.residue(p)),
                'full-word modular comparison failed')


def audit(seconds=90):
    from mmgroup import MM
    from importlib.metadata import version
    require(0<seconds<=90,'bounded source execution')
    deadline=monotonic()+seconds
    rows=[]
    # Include symmetric-square, short-vector and twisted coordinates.
    for tag,idx in [('t',24),('t',852),('l',0),('l',98580),('l',147732),('x',98580)]:
        if monotonic()>=deadline:break
        g=MM(tag,1);v=unit(idx)
        try:
            w=action(v,g,deadline);verify(v,w,g)
            back=action(w,g**-1,deadline)
            require(back.same(v),'dyadic original source inverse')
        except TimeoutError:break
        rows.append(dict(atom=tag,index=idx,nonzero=len(w.sparse()),denominator_power=w.power,
                         output_sha256=w.digest(),inverse=True))
    return dict(status='actual_dyadic_source_atom_audit' if len(rows)==6 else 'bounded_incomplete',
                mmgroup_version=version('mmgroup'),crt_moduli=MODULI,crt_product=MODULUS,
                source_atom_denominator_scale=SCALE,row_l1_bound=ROW_L1_BOUND,
                completed=len(rows),rows=rows,original_JMD_uv_identified=False,
                original_FLM_product_or_VOA_identified=False)


def export(a):
    from mmgroup import MM
    from importlib.metadata import version
    raw=a.manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==a.manifest_sha256,'actual source word manifest SHA')
    m=json.loads(raw)
    require(m['basis']=='Conway-Seysen-MMV-external-196884' and m['source_ref'] and
            set(m['words'])=={'u','v'} and a.generator in m['words'],'actual source basis and words')
    require(0<=a.start<DIM and 1<=a.count<=DIM-a.start,'bounded source columns')
    g=MM(m['words'][a.generator])
    deadline=monotonic()+a.seconds
    a.output.parent.mkdir(parents=True,exist_ok=True)
    count=0
    with a.output.open('x') as f:
        for i in range(a.start,a.start+a.count):
            if monotonic()>=deadline:break
            v=unit(i)
            try:w=action(v,g,deadline)
            except TimeoutError:break
            verify(v,w,g)
            f.write(json.dumps(dict(generator=a.generator,column=i,rows=w.sparse()),sort_keys=True)+'\n')
            f.flush();count+=1
    result=dict(status='source_column_shard',basis=m['basis'],source_ref=m['source_ref'],
        manifest_sha256=a.manifest_sha256,mmgroup_version=version('mmgroup'),
        generator=a.generator,start=a.start,columns=count,next_column=a.start+count,
        shard_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),
        all_requested_columns_complete=count==a.count,original_JMD_FLm_alignment_certified=False)
    with a.output.with_suffix(a.output.suffix+'.receipt.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    return result


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=90)
    p.add_argument('--manifest',type=Path);p.add_argument('--manifest-sha256')
    p.add_argument('--generator',choices=('u','v'));p.add_argument('--start',type=int,default=0)
    p.add_argument('--count',type=int,default=1);p.add_argument('--output',type=Path)
    a=p.parse_args();require(0<a.seconds<=90,'source time budget')
    if a.manifest:
        require(a.manifest_sha256 and a.generator and a.output,'actual source column shard scope')
        r=export(a)
    else:
        r=audit(a.seconds)
        if a.output:
            a.output.parent.mkdir(parents=True,exist_ok=True)
            with a.output.open('x') as f:json.dump(r,f,indent=2);f.write('\n')
    print(json.dumps(r,indent=2))
    if r.get('status')=='bounded_incomplete' or r.get('all_requested_columns_complete') is False:raise SystemExit(2)


if __name__=='__main__':main()
