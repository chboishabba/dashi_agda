"""Endpoint-first same-source inverse: signed independent receiver channels.
Exact linear local inverse/identifiability theorem; no assumed physical
susceptibilities. Source and calibration matrices must come from actual owners.
"""
import sympy as s

def solve(A,y):
    if A.rows!=y.rows or y.cols!=1: raise ValueError("shape")
    # left null witnesses are the exact obstruction to endpoint attainment
    bad=[(z,(z.T*y)[0]) for z in A.T.nullspace() if s.simplify((z.T*y)[0])!=0]
    if bad:return {"status":"INCOMPATIBLE","witnesses":bad}
    x,params=A.gauss_jordan_solve(y)
    return {"status":"COMPATIBLE_LINEAR_MODEL","particular":x.subs(dict.fromkeys(params,0)),"kernel":A.nullspace()}

def main():
    # Observable order: neutral geodesic, support, pickup, independent clock/tide.
    # Manufactured calibration only. Columns: source gravity, ordinary force,
    # pickup; retain clock/tide as a distinct response rather than fitted gain.
    A=s.Matrix([[1,0,0],[1,1,0],[0,0,1],[2,0,0]])
    y=s.Matrix([1,1,0,2]); r=solve(A,y)
    assert r["status"]=="COMPATIBLE_LINEAR_MODEL" and A*r["particular"]==y and not r["kernel"]
    bad=solve(A,s.Matrix([1,1,0,0]))
    assert bad["status"]=="INCOMPATIBLE"
    for z,w in bad["witnesses"]: assert z.T*A==s.zeros(1,A.cols) and w!=0
    # Support-only observation cannot identify gravity vs ordinary force.
    r=solve(A[1:2,:],s.Matrix([1]))
    assert len(r["kernel"])==2
    assert A[1:2,:]*s.Matrix([1,-1,0])==s.zeros(1,1)
    # Reverse target at specified positive energy metric H: minimum-norm
    # feasible source, not a claim that such a source is physically available.
    B=s.Matrix([[1,2,0],[0,1,1]]); H=s.diag(2,3,5); target=s.Matrix([1,0])
    K=B*H.inv()*B.T; x=H.inv()*B.T*K.inv()*target
    assert B*x==target
    for z in B.nullspace(): assert (z.T*H*x)[0]==0
    assert (x.T*H*x)[0]==(target.T*K.inv()*target)[0]
    print("PASS signed left-null obstruction, source identifiability, minimum positive energy inverse")
    print("OPEN actual lane-specific calibrated Jacobians, nonlinear reachable sets and physical receivers")
if __name__=="__main__":main()
