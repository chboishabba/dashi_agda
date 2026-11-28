"""Independent SymPy GF(3) rank audit; input is existing H28 native fixture."""
from pathlib import Path
import json
from collections import defaultdict
from sympy import Matrix, GF, __version__
from sympy.polys.matrices import DomainMatrix
alphabet='אבגדהוזחטיכלמנסעפצקרשתךםןףץ'
fixture=json.loads(Path('Docs/support/reference/TorahCryptoCorpus20261125/h28-native-word-fixture.json').read_text())
def audit(triples):
    m=Matrix([[t.count(g)%3 for g in alphabet] for t in triples])
    dm=DomainMatrix.from_Matrix(m).convert_to(GF(3))
    rank=dm.rank(); basis=dm.nullspace().to_Matrix(); groups=defaultdict(list)
    assert all(int(x)%3==0 for x in m*basis.T)
    for j,g in enumerate(alphabet):
        groups[tuple(int(basis[i,j])%3 for i in range(basis.rows))].append(g)
    return rank,len(groups),list(groups.values())
all_triples=[]
for w,expected in zip(fixture,[(18,9),(23,4),(3,27),(23,4)]):
    a,b,c=[''.join(word['glyphs'] for word in r['words']) for r in w['rows']]
    assert len(a)==len(b)==len(c)
    ts=list(zip(a,b[::-1],c)); all_triples+=ts
    result=audit([t for t in ts if len(set(t))==3])
    assert result[:2]==expected
    print(w['book'],w['ch'],w['v'],result,'all rank/classes',audit(ts)[:2])
assert audit([t for t in all_triples if len(set(t))==3])[:2]==(25,2)
assert audit(all_triples)[:2]==(26,1)
print('SymPy',__version__,'PASS')
