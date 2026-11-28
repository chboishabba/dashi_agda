"""Independent candidate replay. No original certificate admission.
Run after ns369_similarity_reconstruct.py. Uses actual source basis and
coefficients, not surrogate amplitudes. Bounded Cartesian cells only.
"""
import argparse, json, time
from pathlib import Path
from itertools import product
import numpy as np
import sympy as S
from mpmath import iv
from ns369_similarity_reconstruct import build_basis, grid, matrices, operators, save, xyz, FIELDS
from ns_cell_scalar_budget import choose_sup
from fractions import Fraction

s=S.Symbol("s", real=True)

def exact(v):
    return S.Rational(float(v))

def profile(basis,c):
    W=S.zeros(3,1); p=S.Integer(0)
    for (k,a,t,j,part,v,q),b in zip(basis,c):
        phase=S.exp(S.I*k*s)
        W+=exact(b)*v*phase
        p+=exact(b)*q*phase
    return W,p

def interval_eval(e,env,memo):
    if e in memo:return memo[e]
    if e in env:r=env[e]
    elif e==S.I:r=iv.mpc(0,1)
    elif e.is_Rational:r=iv.mpf(int(e.p))/iv.mpf(int(e.q))
    elif e.is_Float:r=interval_eval(S.Rational(e),env,memo)
    elif e==S.pi:r=iv.pi
    elif e.is_Add:r=sum((interval_eval(t,env,memo) for t in e.args),iv.mpf(0))
    elif e.is_Mul:
        r=iv.mpf(1)
        for t in e.args:r*=interval_eval(t,env,memo)
    elif e.is_Pow:
        b=interval_eval(e.base,env,memo)
        if e.exp.is_Integer:r=b**int(e.exp)
        else:r=iv.exp(interval_eval(e.exp,env,memo)*iv.ln(b))
    elif e.func==S.exp:r=iv.exp(interval_eval(e.args[0],env,memo))
    else:raise ValueError("unsupported interval expression: "+str(e.func))
    memo[e]=r
    return r

def real_interval(e,env,memo):
    return interval_eval(e,env,memo).real

def bounds(v):
    # Preserve interval endpoints as exact dyadic rational strings, not
    # nearest-rounded JSON floats.
    def q(t):
        sign,man,exponent,bc=t
        if bc<0:raise ValueError("nonfinite enclosure")
        return str(Fraction((-1 if sign else 1)*man)*Fraction(2)**exponent)
    return [q(t) for t in v._mpi_]

def physical_basis(basis):
    return [(v*S.exp(S.I*k*s),p*S.exp(S.I*k*s)) for k,a,t,j,part,v,p in basis]

def adjoint_samples(basis,M,pts,phase,omega,c,deadline):
    from ns369_similarity_reconstruct import ev
    V,G,L,P=M
    W=V@c; DW=G@c
    A=np.zeros_like(L)
    # L* = -omega ds -1 - y.grad/2 - Delta - W.grad + DW^T
    # plus independent adjoint pressure gradient.
    for b,(k,a,t,j,part,v,q) in enumerate(basis):
        if time.monotonic()>deadline:raise TimeoutError("adjoint basis")
        e=np.exp(1j*k*phase)
        for i in range(3):
            f=(-1-S.I*k*S.Float(omega))*v[i]-sum(S.diff(v[i],x,2) for x in xyz)+S.diff(q,xyz[i])
            A[:,i,b]=(e*ev(f,pts)).real
    A-=np.einsum("nijd,nj->nid",G,pts/2+W)
    A+=np.einsum("nji,njd->nid",DW,V)
    return A

def solve_adjoint(basis,M,pts,phase,wt,omega,c,deadline):
    V,G,L,P=M
    A=adjoint_samples(basis,M,pts,phase,omega,c,deadline)
    sw=np.sqrt(wt)[:,None,None]
    F=(A*sw).reshape(-1,len(basis))
    # Normalize against actual velocity mass, remove pressure-only directions
    # from normalization while allowing them in the least squares solve.
    B=(V*sw).reshape(-1,len(basis))
    _,sigma,vt=np.linalg.svd(B,full_matrices=False)
    keep=sigma>max(sigma)*1e-10
    T=vt[keep].T/sigma[keep]
    N=vt[~keep].T
    FN=F@N
    fit=np.linalg.lstsq(FN,F@T,rcond=1e-10)[0] if N.shape[1] else np.zeros((0,T.shape[1]))
    E=T-N@fit
    _,sv,vh=np.linalg.svd(F@E,full_matrices=False)
    d=E@vh[-1]
    r,J,flat,jf=operators(M,wt)
    pairing=float(np.sum(wt[:,None]*(V@d)*r(c)))
    return d,{"adjoint_residual":float(np.linalg.norm(F@d)),
              "velocity_norm":float(np.linalg.norm(B@d)),
              "residual_pairing":pairing,"singular_values":sv.tolist(),
              "pressure_gauge_nullity":int(N.shape[1]),
              "scope":"sampled homogeneous formal adjoint; not original actuator equation"}

def interval_cells(basis,c,d,omega,radius,n,deadline,receipt,out):
    # Differentiate complex modes before real projection. Nonlinear products
    # use real intervals individually, never Re of a complex product.
    iv.dps=30
    W,p=profile(basis,c); H,q=profile(basis,d)
    dw=W.jacobian(xyz); dh=H.jacobian(xyz)
    drift=S.Matrix(xyz)/2
    LW=W/2+exact(omega)*W.diff(s)+dw*drift-W.applyfunc(lambda f:sum(S.diff(f,x,2) for x in xyz))+S.Matrix([S.diff(p,x) for x in xyz])
    LH=-H-exact(omega)*H.diff(s)-dh*drift-H.applyfunc(lambda f:sum(S.diff(f,x,2) for x in xyz))+S.Matrix([S.diff(q,x) for x in xyz])
    modes=physical_basis(basis)
    for idx in product(range(n),repeat=4):
        if time.monotonic()>deadline:raise TimeoutError("interval cells")
        env={}
        for x,i in zip(xyz,idx[:3]):
            a=Fraction(-radius)+Fraction(2*radius*i,n)
            b=a+Fraction(2*radius,n)
            lo=iv.mpf(a.numerator)/a.denominator
            hi=iv.mpf(b.numerator)/b.denominator
            env[x]=iv.mpf([lo.a,hi.b])
        a=2*iv.pi*idx[3]/n;b=2*iv.pi*(idx[3]+1)/n
        env[s]=iv.mpf([a.a,b.b])
        memo={}
        w=[real_interval(e,env,memo) for e in W]
        h=[real_interval(e,env,memo) for e in H]
        g=[[real_interval(dw[i,j],env,memo) for j in range(3)] for i in range(3)]
        k=[[real_interval(dh[i,j],env,memo) for j in range(3)] for i in range(3)]
        residual=[real_interval(LW[i],env,memo)+sum(g[i][j]*w[j] for j in range(3)) for i in range(3)]
        adjoint=[real_interval(LH[i],env,memo)+sum(g[j][i]*h[j]-k[i][j]*w[j] for j in range(3)) for i in range(3)]
        v=[[real_interval(e,env,memo) for e in m[0]] for m in modes]
        # Pointwise integrand intervals; multiplying by exact cell volume
        # and summing gives integral bounds on the compact box.
        mass=[];stretch=[]
        for va in v:
            mass.append([bounds(sum((va[i]*vb[i] for i in range(3)),iv.mpf(0))) for vb in v])
            stretch.append([bounds(sum((va[i]*(g[i][j]+g[j][i])*vb[j]/2 for i in range(3) for j in range(3)),iv.mpf(0))) for vb in v])
        volume=(iv.mpf(2*radius)/n)**3*2*iv.pi/n
        receipt["cells"].append({"index":idx,"volume":bounds(volume),"momentum":[bounds(v) for v in residual],
            "adjoint":[bounds(v) for v in adjoint],"mass_integrand":mass,"stretch_integrand":stretch,
            "divergence":bounds(sum(g[i][i] for i in range(3)))})
        save(out,receipt)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("candidate",type=Path)
    p.add_argument("--out",type=Path,default=Path("Artifacts/ns369_certificate_replay.json"))
    p.add_argument("--seconds",type=float,default=90)
    p.add_argument("--radius",type=int,default=2)
    p.add_argument("--cells",type=int,default=2)
    p.add_argument("--grid",type=int,default=3)
    p.add_argument("--budget",type=Path)
    args=p.parse_args()
    if min(args.seconds,args.radius,args.cells,args.grid)<=0:p.error("positive parameters required")
    deadline=time.monotonic()+args.seconds
    data=json.loads(args.candidate.read_text())
    receipt={"status":"started","fields":{f:"unpaid" for f in FIELDS},"cells":[],
             "scope":"compact interval replay of independent trial profile; no global certificate",
             "candidate":str(args.candidate)}
    save(args.out,receipt)
    try:
        c=np.asarray(data["coefficients"],dtype=float)
        if not np.isfinite(c).all():raise ValueError("nonfinite coefficients")
        omega=2*np.pi/data["period"]
        level=max(max(abs(b[0]),abs(b[1]),b[3]) for b in data["basis"])
        basis=build_basis(level,omega)
        if [list(b[:5]) for b in basis]!=data["basis"] or len(c)!=len(basis):
            raise ValueError("basis mismatch")
        pts,phase,wt=grid(args.grid,args.grid,4*level+1,4*level+1)
        M=matrices(basis,pts,phase,omega,deadline)
        r,J,flat,jf=operators(M,wt)
        norm=float(np.linalg.norm((M[0]@c)*np.sqrt(wt)[:,None]))
        receipt["profile"]={"velocity_norm":norm,"residual":float(np.linalg.norm(flat(r(c)))),
            "nontrivial_sample":norm>1e-8,
            "unforced_stage":data["history"][-1]["force_fraction"]==0}
        save(args.out,receipt)
        if norm<=1e-8 or not receipt["profile"]["unforced_stage"]:
            raise ValueError("zero or still-forced candidate")
        d,diag=solve_adjoint(basis,M,pts,phase,wt,omega,c,deadline)
        receipt["adjoint"]=diag
        receipt["adjoint_coefficients"]=d.tolist()
        save(args.out,receipt)
        if args.budget:
            vals=json.loads(args.budget.read_text())
            receipt["conditional_budget_sup"]=str(choose_sup(*(Fraction(str(v)) for v in vals)))
            receipt["budget_scope"]="externally supplied scalars; not paid by trial profile"
        interval_cells(basis,c,d,omega,args.radius,args.cells,deadline,receipt,args.out)
        receipt["status"]="compact_replay_complete_not_certified"
    except TimeoutError as e:
        receipt["status"]="checkpoint_timeout";receipt["reason"]=str(e)
    except Exception as e:
        receipt["status"]="failed";receipt["reason"]=repr(e)
        save(args.out,receipt);raise
    save(args.out,receipt)
    print(receipt["status"],args.out)

if __name__=="__main__":main()
