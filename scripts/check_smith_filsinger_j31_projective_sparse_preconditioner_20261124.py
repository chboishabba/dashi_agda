#!/usr/bin/env python3
"""J31 projective 69D/15D residual preconditioner and conditional rational cone.

Cross-programme donors: P vs NP #1548, Pi #1546, Langlands/GCT #1549.
DONOR analogies and a numerical central Jacobian do not prove the Filsinger
periodic orbit. The seven source ODE chart interval enclosures are still OPEN.
"""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

def mm(a,b):
    if not a:return []
    if not b:return [[] for _ in a]
    m=len(b);assert all(len(row)==m for row in a)
    n=len(b[0]);assert all(len(row)==n for row in b)
    bt=list(zip(*b));z=Q(0)
    return [[sum((x*y for x,y in zip(row,col)),z) for col in bt] for row in a]

def add(a,b,sgn=1):
    assert len(a)==len(b)
    return [[x+sgn*y for x,y in zip(ar,br)] for ar,br in zip(a,b)]

def eye(n):return [[Q(int(i==j)) for j in range(n)] for i in range(n)]

def block(a,b):return [x+y for x,y in zip(a,b)]

def unit_lower_inverse(h):
    """Exact inverse of the source 54x54 matching lower-triangular block."""
    n=len(h);assert all(len(row)==n for row in h)
    assert all(h[i][i]==1 and all(h[i][j]==0 for j in range(i+1,n)) for i in range(n))
    out=eye(n)
    for i in range(n):
        for j in range(i):
            out[i][j]=-sum((h[i][k]*out[k][j] for k in range(i)),Q(0))
    assert mm(h,out)==eye(n)
    return out

def extract(j):
    """Rows [54 matching,9 return,6 guard]; cols [x0,y1..y6,t1..t6]."""
    assert len(j)==69 and all(len(r)==69 for r in j)
    u=list(range(9))+list(range(63,69));v=list(range(9,63))
    take=lambda rows,cols:[[j[i][k] for k in cols] for i in rows]
    return (take(range(54),u),take(range(54),v),
            take(range(54,69),u),take(range(54,69),v))

def preconditioner_parts(hu,hv,ru,rv,b):
    """Exact Schur identity for a rational 15D approximate inverse B.

    T=Hv^-1; L=Rv*T; S=Ru-L*Hu.
    C = [-B*L, B; T+T*Hu*B*L, -T*Hu*B].
    I-C*A = [I-B*S,0; -T*Hu*(I-B*S),0].
    """
    t=unit_lower_inverse(hv);l=mm(rv,t);s=add(ru,mm(l,hu),-1)
    p=mm(b,l);th=mm(t,hu)
    ctop=block([[-x for x in row] for row in p],b)
    cbottom=block(add(t,mm(th,p)),[[-x for x in row] for row in mm(th,b)])
    c=ctop+cbottom
    e=add(eye(15),mm(b,s),-1)
    predicted=block(e,[[Q(0)]*54 for _ in range(15)])+block(
        [[-x for x in row] for row in mm(th,e)],[[Q(0)]*54 for _ in range(54)])
    a=[hu[i]+hv[i] for i in range(54)]+[ru[i]+rv[i] for i in range(15)]
    assert add(eye(69),mm(c,a),-1)==predicted
    return c,s,t,predicted

def iv(lo,hi=None):
    a=Q(lo);b=a if hi is None else Q(hi)
    assert a<=b
    return a,b

def ivabs(a):return max(abs(a[0]),abs(a[1]))

def ivadd(a,b):return a[0]+b[0],a[1]+b[1]

def ivscale(c,a):return (c*a[0],c*a[1]) if c>=0 else (c*a[1],c*a[0])

def krawczyk_row_gate(f,df,c,r):
    """Exact output-aligned strict row slack, no floating-point comparison.

    Conditional on separately proved source-flow enclosures F(z0) and DF(B).
    """
    n=len(c);assert len(f)==len(df)==len(r)==n
    assert all(len(row)==n for row in df+c)
    assert all(x>0 for x in r)
    slack=[];defect=[];cross=[]
    for i in range(n):
        v=(Q(0),Q(0))
        for k in range(n):v=ivadd(v,ivscale(c[i][k],f[k]))
        d=ivabs(v);w_sum=Q(0)
        for j in range(n):
            w=iv(int(i==j))
            for k in range(n):
                if c[i][k]:w=ivadd(w,ivscale(-c[i][k],df[k][j]))
            w_sum+=r[j]*ivabs(w)
        defect.append(d);cross.append(w_sum);slack.append(r[i]-d-w_sum)
    return dict(all_positive=all(x>0 for x in slack),
                min_slack=str(min(slack)),
                strict_positive_count=sum(x>0 for x in slack),
                slack=[str(x) for x in slack],
                defect=[str(x) for x in defect],
                cross=[str(x) for x in cross])


def rational_chart_transport(f,df,c,r,coordinate_gauge,equation_gauge):
    """Invertible positive rational chart preserving original source/residuals.

    z=z0+D*w, F'(w)=E*F(z0+D*w), C'=D^-1*C*E^-1.
    Strict row slack_i' = row slack_i / D_ii, an EXACT identity.
    An arbitrary lossy quotient is NOT an invertible coordinate chart.
    """
    n=len(r)
    assert len(coordinate_gauge)==len(equation_gauge)==n
    d=list(map(Q,coordinate_gauge));e=list(map(Q,equation_gauge))
    assert all(x>0 for x in d+e)
    ff=[ivscale(e[i],f[i]) for i in range(n)]
    dd=[[ivscale(e[i]*d[j],df[i][j]) for j in range(n)] for i in range(n)]
    cc=[[c[i][k]/(d[i]*e[k]) for k in range(n)] for i in range(n)]
    rr=[r[i]/d[i] for i in range(n)]
    return ff,dd,cc,rr

def exact_fixture():
    """Exact nontrivial source-shaped 69D Schur; retained signed mismatch."""
    hu=[[Q(0)]*15 for _ in range(54)];hv=eye(54)
    rv=[[Q(0)]*54 for _ in range(15)]
    for event in range(6):
        for i in range(9):
            k=9*event+i
            if event:hv[k][k-9]=-Q(1,3)
            hu[k][i]=-Q(1,2) if event==0 else Q(0)
        rv[9+event][9*event+4]=Q((-1)**event,2)
    for i in range(9):rv[i][45+i]=Q(1,4)
    t=unit_lower_inverse(hv);l=mm(rv,t)
    ru=add(eye(15),mm(l,hu))
    c,s,_,res=preconditioner_parts(hu,hv,ru,rv,eye(15))
    assert s==eye(15) and not any(any(x for x in row) for row in res)
    F=[iv(0) for _ in range(69)];F[0]=iv(Q(1,10**12))
    A=[hu[i]+hv[i] for i in range(54)]+[ru[i]+rv[i] for i in range(15)]
    DF=[[iv(x) for x in row] for row in A]
    radius=[Q(1,10**6)]*69
    paid=krawczyk_row_gate(F,DF,c,radius)
    assert paid["all_positive"] and paid["strict_positive_count"]==69
    bad=F[:];bad[0]=iv(Q(1,1000))
    assert not krawczyk_row_gate(bad,DF,c,radius)["all_positive"]
    assert all(x==iv(0) for x in bad[54:])
    # Paper 9 projective gauge: positive invertible chart must exactly reopen
    # all source coordinates, including the signed matching residuals.
    dvec=[Q(2 if i%3==0 else 3 if i%3==1 else 5) for i in range(69)]
    evec=[Q(3 if i%2==0 else 7) for i in range(69)]
    gf,gdf,gc,gr=rational_chart_transport(F,DF,c,radius,dvec,evec)
    chart=krawczyk_row_gate(gf,gdf,gc,gr)
    assert chart["all_positive"]
    assert [Q(x) for x in chart["slack"]]==[
        Q(x)/dvec[i] for i,x in enumerate(paid["slack"])]

    return dict(status="PASS_EXACT_RATIONAL_69D_PROJECTIVE_RESIDUAL_FIXTURE",
        matching_variables=54,quotient_variables=15,independent_equations=69,
        exact_schur_block_identity=True,exact_positive_row_slacks=69,coordinate_chart_slack_equivalence_passed=True,
        deliberately_hidden_matching_residual_rejected=True,
        original_source_interval_verified=False,periodic_orbit_proved=False)

def source_numeric():
    """Original seven physical charts: numerical centre diagnostic ONLY."""
    import numpy as np
    import check_smith_filsinger_j31_source_15d_69d_shooting_20261124 as j31
    import independent_full_period_numerical_audit as native
    z=np.r_[native.root0,j31.TIMES]
    shot=j31.fifteen(z);times=shot["times"]
    states=shot["states"][:7];phi=shot["Phi"]
    J=np.zeros((69,69))
    for k in range(7):
        start=states[k];end=shot["states"][k+1]
        before=j31.mode_f(times[k],start,j31.MODES[k])
        after=j31.mode_f(times[k+1],end,j31.MODES[k])
        rows=slice(9*k,9*(k+1)) if k<6 else slice(54,63)
        if k<6:
            J[rows,9*k:9*(k+1)]=-phi[k]
            J[rows,9*(k+1):9*(k+2)]=np.eye(9)
            J[rows,63+k]=-after
        else:
            J[rows,:9]=-np.eye(9);J[rows,54:63]=phi[k]
        if k>0:J[rows,63+k-1]=(-phi[k]@before if k==6 else phi[k]@before)
    for k in range(6):
        J[63+k,9*(k+1):9*(k+2)]=j31.normal(k)
    u=np.r_[np.arange(9),np.arange(63,69)]
    v=np.arange(9,63)
    hu=J[:54,u];hv=J[:54,v];ru=J[54:,u];rv=J[54:,v]
    assert np.allclose(np.triu(hv),np.eye(54),atol=0,rtol=0)
    T=np.linalg.solve(hv,np.eye(54));L=rv@T
    S=ru-L@hu
    schur_gap=float(np.linalg.norm(S-shot["J"],np.inf))
    assert schur_gap<2e-10
    B=np.array([[float(Q(round(float(x)*10**12),10**12)) for x in row]
                for row in np.linalg.inv(S)])
    P=B@L;TH=T@hu
    C=np.block([[-P,B],[T+TH@P,-TH@B]])
    A=np.block([[hu,hv],[ru,rv]])
    err=float(np.linalg.norm(np.eye(69)-C@A,np.inf))
    E=np.eye(15)-B@S
    predicted=np.block([[E,np.zeros((15,54))],[-TH@E,np.zeros((54,54))]])
    gap=float(np.linalg.norm((np.eye(69)-C@A)-predicted,np.inf))
    assert err<3e-8 and gap<3e-8
    return dict(status="PASS_NUMERICAL_ORIGINAL_J31_PROJECTIVE_PRECONDITIONER",
        schur_to_original_15D_inf=schur_gap,
        original_source_J69_nonzero_entries=int(np.count_nonzero(J)),
        preconditioner_I_minus_CJ_inf=err,
        predicted_block_residual_gap_inf=gap,
        labelled_interface_equations=54,
        original_source_interval_verified=False,
        periodic_orbit_proved=False)

def verify_json(path):
    x=json.loads(Path(path).read_text())
    assert x["format"]=="J31_69D_INTERVAL_CONE_V1"
    assert x["source_scope"]=="ORIGINAL_FILSINGER_J25_J31_SYNTHETIC_NINE_STATE"
    assert x["model_dimension"]==69 and x["mode_count"]==7 and x["event_count"]==6
    c=[[Q(z) for z in row] for row in x["rational_preconditioner"]]
    r=list(map(Q,x["radii"]))
    f=[iv(*a) for a in x["source_F_intervals"]]
    df=[[iv(*a) for a in row] for row in x["source_DF_intervals"]]
    result=krawczyk_row_gate(f,df,c,r)
    result.update(status=("PASS_CONDITIONAL_69D_ROW_INCLUSION_ONLY"
                   if result["all_positive"] else "FAIL_CLOSED_ROW_INCLUSION"),
        source_interval_proof_checked_here=False,
        original_ODE_charts_validated_here=False,
        exact_periodic_orbit_proved=False)
    return result

def main():
    ap=argparse.ArgumentParser()
    modes=ap.add_mutually_exclusive_group(required=True)
    modes.add_argument("--exact-fixture",action="store_true")
    modes.add_argument("--numeric-source",action="store_true")
    modes.add_argument("--verify-json",type=Path)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    result=(exact_fixture() if args.exact_fixture else
            source_numeric() if args.numeric_source else verify_json(args.verify_json))
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=="__main__":main()
