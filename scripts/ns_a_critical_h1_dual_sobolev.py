"""A: same-source H1 -> critical stationary Stokes and Duhamel bounds.

Provenance: classical homogeneous Sobolev embeddings, duality, Leray
projection, H1 interpolation, Jensen/Tonelli and Leray energy inequality.
Not a new PDE theorem or proof of Clay A.

Let E(t)=||u||²_L2, D(t)=||grad u||²_L2 and u be divergence-free.
Let g=div(u tensor u), V=(-nu Delta)^(-1)P g, W the causal
nonlinear heat/Duhamel response. In R³:
  ||V||_{dot H^(1/2)} <= C_S/nu ||u tensor u||_(L^(3/2))
                       <= C_S/nu ||u||_L3²
                       <= (C_S*C_6)/nu sqrt(E D).
Here C_S is the dual dot-H^(1/2)->L3 constant (including the
Fourier-normalization convention) and C_6 is the H1->L6 constant.

The proof is source-specific: divergence contributes |xi|, Stokes
inverse contributes |xi|^-2 and the Leray projection is an L2
Fourier contraction. Thus for F=u tensor u,
  ||V||_{dot H^(1/2)} <= nu^-1 ||F||_{dot H^(-1/2)}.

For an unforced Leray solution with E(t)<=E0 and
int_0^T D(t)dt <= E0/(2nu), Jensen/Tonelli imply
 int_0^T ||W(t)||²_{dot H^(1/2)} dt
   <= C_S²*C_6²*E0²/(2nu³).
This is UNIFORM in T but time-L2 dot-H^(1/2) is not a
critical spacetime norm under NS scaling, and is not A3.

The earlier three-region conditional H2 logarithmic estimate
scripts/ns_a_critical_h2_log_majorant.py is weaker and not the
canonical A source estimate. No Bishop/Lean kernel receipt here.
"""
import sympy as S

def certificate():
    e,d,nu,t,lam,CS,C6=S.symbols(
        "E D nu T lambda C_S C_6",positive=True)
    power_interp=S.Rational(1,2)*S.Rational(1,2)+S.Rational(1,2)*S.Rational(1,6)
    assert power_interp==S.Rational(1,3)
    K=CS*C6
    spatial=K**2*e*d/nu**2
    scaled=S.simplify(spatial.subs({e:e/lam,d:d*lam},simultaneous=True))
    assert S.simplify(scaled-spatial)==0
    spacetime=S.simplify(K**2/nu**2*e*(e/(2*nu)))
    assert spacetime==K**2*e**2/(2*nu**3)
    # W_lambda(t,x)=lambda W(lambda^2*t,lambda*x),
    # so the L2_t dot-Hhalf norm squared scales as lambda^-2.
    assert S.simplify(lam**(-2)-1)!=0
    # Available energy interpolation yields L4_t L3_x, not Serrin:
    assert S.Rational(2,4)+S.Rational(3,3)==S.Rational(3,2)
    assert S.Rational(2,4)+S.Rational(3,3)>1
    return {"same_source":"(-nu Delta)^(-1) P div(u tensor u)",
            "norm":"physical homogeneous H^(1/2)",
            "instantaneous_bound_squared":str(spatial),
            "uniform_time_integrated_bound_squared":str(spacetime),
            "critical_spatial_scaling":True,
            "time_integrated_scaling":"lambda^-2; not critical in spacetime",
            "not_claimed":["A3 continuation","uniform sup_t L3","kernel proof"]}

if __name__=="__main__":
    print(certificate())
