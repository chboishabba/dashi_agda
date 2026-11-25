#!/usr/bin/env python3
"""Original 3B parity ranks from two character values, no vacuum basis search.

Separate native source audit. No change to active char0 checkpoint files.
The reduction of the modulation average uses literal inversion by C^2.
"""
import argparse, hashlib, json
from pathlib import Path
from fractions import Fraction

DIM=196884
SOURCE='c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2'
def require(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def integer(x):
    require(x.denominator==1,'nonintegral rank or trace')
    return int(x)
def ranks(dim,z,j,zj,n=6):
    """Inputs are FULL W traces (including trivial line), not Irr196883."""
    d=3**n
    phase=integer(Fraction(dim-z,3));zero=dim-2*phase
    vacuum=integer(Fraction(phase,d));tau=integer(Fraction(j-zj,3))
    minus=integer(Fraction(vacuum-tau,2));plus=integer(Fraction(vacuum+tau,2))
    zero_trace=integer(Fraction(j+2*zj,3))
    zero_minus=integer(Fraction(zero-zero_trace,2));zero_plus=integer(Fraction(zero+zero_trace,2))
    require(min(phase,zero,minus,plus,zero_minus,zero_plus)>=0,'negative rank')
    return dict(phase_dimension=phase,zero_dimension=zero,vacuum_dimension=vacuum,
                vacuum_parity_trace=tau,negative_rank=minus,positive_rank=plus,
                zero_sector_j_trace=zero_trace,zero_sector_j_negative_rank=zero_minus,
                zero_sector_j_positive_rank=zero_plus)

def run(a):
    from mmgroup import MM
    from importlib.metadata import version
    m,c=read(a.manifest),read(a.cover)
    require(m['source_blob_sha']==c['original_source_blob_sha']==SOURCE and c.get('actual_mmgroup_used') is True,'original source mismatch')
    z=MM(m['center_word']);C=MM(c['canonical_C_word']);j=C**2;one=z**0
    B=[MM(w) for w in m['modulation_words']]
    T=[MM(w) for w in m['translation_words']]
    require(len(B)==len(T)==6 and z.order()==3 and C.order()==4 and j.order()==2,'literal orders')
    require(C*z*C**-1==z**-1 and j*z==z*j,'literal signed central action')
    require(all(b.order()==3 and b*z==z*b and j*b*j**-1==b**-1 for b in B),'literal modulation inversion')
    require(all(t.order()==3 and t*z==z*t for t in T),'literal translation axes')
    require(all(B[i]*T[k]==z**int(i==k)*T[k]*B[i] and B[i]*B[k]==B[k]*B[i] and T[i]*T[k]==T[k]*T[i] for i in range(6) for k in range(6)),'literal marked Weyl chart')
    require(z.in_G_x0() and int(z.chi_G_x0()[0])==53,'original marked 3B character')
    # One conjugator for j and its commuting central twists. Verify actual
    # equality to the standard 2B involution before evaluating the character.
    typ,h=j.conjugate_involution(ntrials=a.ntrials)
    require(typ==2 and h**-1*j*h==MM('x',0x1000),'2B conjugator unavailable; retain residual')
    def trace(g):
        u=h**-1*g*h
        require(u.in_G_x0(),'conjugated word outside G_x0')
        vals=tuple(int(x) for x in u.chi_G_x0())
        return dict(word=str(g),conjugated_word=str(u),irreducible_character=vals[0],full_character=vals[0]+1,components=list(vals))
    traces={name:trace(g) for name,g in [('j',j),('zj',z*j),('z2j',z**2*j),('C',C)]}
    require(traces['zj']['full_character']==traces['z2j']['full_character'],'central twist conjugacy residual')
    r=ranks(DIM,54,traces['j']['full_character'],traces['zj']['full_character'])
    require(r['vacuum_dimension']==90,'actual vacuum rank residual')
    return dict(status='ACTUAL_LITERAL_PARITY_TRACE_REPLAY',manifest_sha256=sha(a.manifest),cover_sha256=sha(a.cover),
                mmgroup_version=version('mmgroup'),conjugator=str(h),traces=traces,derived=r,
                expected_12_78_matches=(r['negative_rank'],r['positive_rank'])==(12,78),
                original_outer_character_observed=traces['C']['irreducible_character'],
                full_source_character_descent_authenticated=False,
                exact_numeric_intertwiner_computed=False,
                premise='original Conway representation and authenticated E/normalizer; parity ranks from literal Weyl chart and B inversion')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('manifest','cover','out'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--ntrials',type=int,default=100);a=p.parse_args()
    if a.out.exists():p.error('refusing to overwrite receipt')
    a.out.parent.mkdir(parents=True,exist_ok=True)
    try:r=run(a)
    except Exception as exc:r=dict(status='BLOCKED_OR_SOURCE_RESIDUAL',error=repr(exc))
    a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
    return 0 if r.get('status')=='ACTUAL_LITERAL_PARITY_TRACE_REPLAY' and r.get('expected_12_78_matches') else 2
if __name__=='__main__':raise SystemExit(main())
