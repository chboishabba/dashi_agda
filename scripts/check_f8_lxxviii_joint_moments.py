"""Exact rational joint weak-load moment witnesses and receiver-dual controls.
Reuse check_f8_lxxv_taylor and ksw668_f8_weak_source; no new integration
engine or adjoint propagation. Binary64 source values are treated exactly.
The rational dimensionless mesh is an idealization of the native float mesh.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import ceil
import numpy as np

def moment_rows(h):
    n=ceil(1/h)+1
    rows=[[Q(0)]*(3*n) for _ in range(4)]
    for i in range(n):
        x=(i*h)**2
        rows[0][i]=1
        rows[1][i]=x
        rows[2][n+i]=1
        rows[3][n+i]=9*x
        rows[3][2*n+i]=-40
    return rows

def apply(rows,vec):
    return [sum((a*b for a,b in zip(row,vec)),Q(0)) for row in rows]

def support(row,lo,hi):
    return sum((max(a*l,a*u) for a,l,u in zip(row,lo,hi)),Q(0))

def dual_upper(c,lo,hi,rows,dlo,dhi,lam):
    """Any rational lambda gives a rigorous box-plus-moment upper bound."""
    assert len(rows)==len(dlo)==len(dhi)==len(lam)
    residual=[x-sum((row[i]*v for row,v in zip(rows,lam)),Q(0)) for i,x in enumerate(c)]
    return support(residual,lo,hi)+support(lam,dlo,dhi)

def exact_witness(lo,hi,rows,target,h):
    """Exact 4x4 pivot correction to midpoint; fail closed if none fits."""
    n=ceil(1/h)+1
    mid=[(a+b)/2 for a,b in zip(lo,hi)]
    widths=[b-a for a,b in zip(lo,hi)]
    q0=sorted(range(n),key=lambda j:widths[j],reverse=True)[:4]
    q2=sorted(range(n),key=lambda j:widths[n+j],reverse=True)[:3]
    q4=sorted(range(n),key=lambda j:widths[2*n+j],reverse=True)[:3]
    for a,b in combinations(q0,2):
      for c in q2:
       for d in q4:
        piv=[a,b,n+c,2*n+d]
        rhs=[v-w for v,w in zip(target,apply(rows,mid))]
        mat=[[row[i] for i in piv] for row in rows]
        for k in range(4):
            p=next((j for j in range(k,4) if mat[j][k]),None)
            if p is None:break
            mat[k],mat[p]=mat[p],mat[k]
            rhs[k],rhs[p]=rhs[p],rhs[k]
            v=mat[k][k]
            mat[k]=[x/v for x in mat[k]];rhs[k]/=v
            for j in range(4):
                if j!=k:
                    v=mat[j][k]
                    mat[j]=[x-v*y for x,y in zip(mat[j],mat[k])]
                    rhs[j]-=v*rhs[k]
        else:
            w=mid.copy()
            for j,x in zip(piv,rhs):w[j]+=x
            if all(a<=x<=b for x,a,b in zip(w,lo,hi)):
                assert apply(rows,w)==target
                return w,piv
    raise AssertionError("no exact rational feasible witness found")

def box_error(enclosures,src,h):
    n=ceil(1/h)+1
    assert len(enclosures)==3 and all(len(v)==n for v in enclosures)
    lo=[];hi=[];bh=[]
    for q in range(3):
        d=3+4*q
        for i in range(n):
            W=((i*h+h/2)**d-max(Q(0),i*h-h/2)**d)/d
            z=Q(float(src[q,i]))*W
            a,b=enclosures[q][i]
            assert a<=z<=b
            bh.append(z);lo.append(a-z);hi.append(b-z)
    rows=moment_rows(h)
    defect=[-x for x in apply(rows,bh)]
    for row,v in zip(rows,defect):
        assert -support([-x for x in row],lo,hi)<=v<=support(row,lo,hi)
    return lo,hi,rows,defect

def control_test():
    h=Q(1,5);rows=moment_rows(h);n=ceil(1/h)+1
    e=[Q(0)]*(3*n);x=[(i*h)**2 for i in range(3)]
    e[0]=x[1]-x[2];e[1]=x[2]-x[0];e[2]=x[0]-x[1]
    e[n]=1;e[n+1]=-1;e[2*n]=9*(x[0]-x[1])/40
    assert apply(rows,e)==[0]*4
    c=[Q((7*i)%19-9,13) for i in range(len(e))]
    ref=[Q(0)]*len(e);ref[0]=Q(1,10**7)
    err=[v-b for v,b in zip(e,ref)]
    lo=[v-Q(1,100) for v in err];hi=[v+Q(1,100) for v in err]
    defect=[-v for v in apply(rows,ref)]
    lam=[Q(3,5),Q(-2,3),Q(1,7),Q(-9,11)]
    actual=sum((a*b for a,b in zip(c,err)),Q(0))
    upper=dual_upper(c,lo,hi,rows,defect,defect,lam)
    lower=-dual_upper([-v for v in c],lo,hi,rows,defect,defect,lam)
    assert lower<=actual<=upper
    return True

def main():
    from check_f8_lxxv_taylor import enclose
    from ksw668_f8_weak_source import weak_source
    assert control_test()
    for h in (Q(1,5),Q(3,20)):
        n=ceil(1/h)+1
        r=np.arange(n+1)*float(h)*.04
        src=weak_source(.04,r,.04*float(h))
        lo,hi,rows,defect=box_error(enclose(h,20),src,h)
        witness,piv=exact_witness(lo,hi,rows,defect,h)
        assert apply(rows,witness)==defect
        print("h=",h,"variables=",len(lo),"constraints=",len(rows),
              "max_float_defect=",max(abs(float(d)) for d in defect),
              "exact_rational_feasible=PASS pivots=",piv,flush=True)
    print("PASS: both exact rational joint-moment witnesses and dual control")

if __name__=="__main__":main()
