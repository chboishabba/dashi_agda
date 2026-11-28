"""Replay the actual bounded normal-fold producer followed by cubic contraction.
Copies have a unique lift, so the independent oracle remains on master trits.
"""
from fractions import Fraction
from check_pnp_quadratic_phase import structured_contrast
from check_pnp_cubic_cnf_source import fixture,oracle
import json
if not __debug__:raise SystemExit('refusing optimized execution')

def add_chain(F,cols,t,R,master,length):
    F=list(F);cols=list(cols);v=master
    for _ in range(length):
        j=len(cols)+1
        F.extend(((-v,j),(v,-j)))
        cols.append((0,)*(len(t)+1));v=j
    return tuple(F),tuple(cols),t,tuple(range(len(cols)))

def main():
    terms=[((0,1,2),1),((3,4,5),1),((2,6),1),((3,6),2),((6,6),1)]
    n=7;count=0;rows=[]
    for copies in (7,8,10,12):
        F,cols,t,R=add_chain(*fixture(n,terms),1,copies)
        for o in range(3):
            a=structured_contrast(F,cols,t,o,R,Fraction(1),8,1,10000000,normal_label_width=3,normal_boundary_width=3,degree_cap=3,phase_branch_cap=256)
            assert a is not None,(copies,o)
            x,y,st=a
            assert x==y==oracle(n,terms,o);count+=1
            assert st['normal_queries']==3 and st['exceptional']==0;count+=1
            assert st['phase_leaves']==9 and st['branches']==1;count+=1
            rows.append(dict(copies=copies,vars=len(R),clauses=len(F),offset=o,stats=st))
        assert structured_contrast(F,cols,t,0,R,Fraction(1),8,1,1,degree_cap=3) is None;count+=1
        assert structured_contrast(F,cols,t,0,R,Fraction(1),8,1,10000000,normal_label_width=0,degree_cap=3) is None;count+=1
    print(json.dumps(dict(checks=count,rows=rows)))
if __name__=='__main__':main()
