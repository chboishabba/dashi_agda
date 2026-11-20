"""Exact signed factorial arithmetic on compact receipt channels (reported digits)."""
import json, sys
from pathlib import Path
import sympy as s

def audit(p):
    d=json.loads(Path(p).read_text(),parse_float=s.Rational)
    assert d['physical_acceptance'] is False
    assert d['geometry']['intrinsic_4D_weyl_spatial_operator']=='full_reconstructed_Delta3'
    assert d['alias']=={'factorial-D':'fine'}
    r=d['rows']; assert len(r)==8
    a,b,c,f=[r[k] for k in ('factorial-A','factorial-B','factorial-C','fine')]
    assert a['actual_dt']==b['actual_dt']==c['actual_dt']==f['actual_dt']
    count=0
    for key in ('E4','E5','E4t','E5t','H','lap','farE4','farE5'):
        out=[]
        for i in range(3):
            A,B,C,D=[s.Rational(x[key][i]) for x in (a,b,c,f)]
            rad=C-A;norm=B-A;inter=D-C-B+A;total=D-A
            assert rad+norm+inter==total;count+=1
            out.append([rad,norm,inter,total])
        print(key,'aggregate', [float(sum(x[j] for x in out)) for j in range(4)])
        if key in ('E4','E5'):
            print('mode rows radial normal interaction total radial_fraction')
            for row in out: print(*[float(z) for z in row],float(row[0]/row[3]))
    for key in ('E4','E5'):
        A,B,C,D=[s.Matrix(x[key]) for x in (a,b,c,f)]
        rad=C-A;nor=B-A;inter=D-C-B+A;total=D-A
        print(key,'sum-absolute mode effects',*[float(sum(abs(z) for z in v)) for v in (rad,nor,inter,total)])
        for x,y in [('coarse','medium'),('medium','fine'),('medium','medium-dt-half'),('fine','fine-dt-half')]:
            X,Y=[s.Matrix(r[k][key]) for k in (x,y)]
            print(key,x,y,'aggregate drift',float(sum(Y-X)), 'sum absolute mode drift',float(sum(abs(z) for z in Y-X)))
    print('exact factorial identities',count,'PASS')
    return count
if __name__=='__main__':audit(sys.argv[1])
