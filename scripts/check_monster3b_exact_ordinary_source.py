"""Exact source-only relators on original Lindsey signed 12D blocks.
Symmetric-square dual functor carries the same word identities to 78D.
"""
import json, hashlib
from pathlib import Path
from monster3b_char0_orbit_weld import *

def run(path):
    data=path.read_bytes();require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()=='b0f96b37494cfca56f116b991d350352d3a493f2','original packet')
    data=json.loads(data);count=0
    # Compute 12D source only, avoiding repeated dense 78D products.
    def ev(g,s):
        r=data[g];return mat([[(K.convert(a[i])+Z**s*K.convert(a[i+1]))/K.convert(r['denominator']) for i in range(0,24,2)] for a in r['numerator_rows']]).transpose()
    C={s:ev('C',s) for s in (1,2)};baseD={s:ev('D',s) for s in (1,2)};I=eye(12)
    for q in range(3):
        D={s:baseD[s].scalarmul(Z**(s*q)) for s in (1,2)}
        E={s:C[s].inv()*D[3-s]*C[s] for s in (1,2)}
        maps={'C':C,'D':D,'E':E,'c':{s:C[3-s].inv() for s in (1,2)},'d':{s:D[s].inv() for s in (1,2)},'e':{s:E[s].inv() for s in (1,2)}}
        def word(w,s):
            A=I;t=s
            for g in w:
                A=maps[g][t]*A
                if g.lower()=='c':t=3-t
            require(s==t,'word changes phase')
            return A
        for s in (1,2):
            R=word('cdcdcddcdd',s);Q=word('CDCDD',s);CD=word('CDCD',s);G=word('DEdeDeDEDEdedEd',s)**3
            tests=[word('CC',s)==I.scalarmul(-K.one),word('DD',s)*D[s]==I,CD**28==I,CD**14==word('CC',s),R**7==I.scalarmul(Z**s),Q**7==I.scalarmul(Z**(s*q)),G**13==I,G!=I]
            require(all(tests),f'exact source residual {q}:{s} {tests}');count+=len(tests)
    print({'exact_original_12d_relators':count,'source_only':True})
if __name__=='__main__':
    import sys
    run(Path(sys.argv[1]))
