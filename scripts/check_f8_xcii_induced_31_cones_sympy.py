"""XII — original moving AdS5 brane induced Lorentz 3+1 and cone comparison.

Consumes original KSW668 F8 clock/brane metric and existing DASHI
Lorentz31/TSFV and KSW brane-bulk causal owners. Does not infer a unique
physical 3+1 dimension from finite cone signatures; does not compute
Weyl waves or detector reception. Local SymPy only; no CI.
"""
import json
import mpmath as mp
import sympy as sp

def audit():
    t,x,y,w=sp.symbols("t x y w",positive=True)
    F=sp.asinh(t)-sp.sqrt(1+t*t)/t
    b=1/t
    # Same ORIGINAL 5D Poincare metric, no substitute KK base.
    g5=sp.diag(-1,1,1,1,1)/b**2
    embed=sp.Matrix([F,x,y,w,b])
    J=embed.jacobian([t,x,y,w])
    induced=(J.T*g5*J).applyfunc(sp.simplify)
    assert induced==sp.diag(-1,t*t,t*t,t*t)
    assert sp.simplify(t*t*(sp.diff(F,t)**2-sp.diff(b,t)**2)-1)==0
    assert sp.simplify(sp.diff(F,t)-sp.sqrt(1+t*t)/t**2)==0
    # Induced FRW radial null condition: |dr/dt|=1/t.
    assert sp.integrate(1/t,(t,1,12))==sp.log(12)
    mp.mp.dps=70
    end=mp.mpf(12)
    f=lambda v:mp.asinh(v)-mp.sqrt(1+v*v)/v
    DT=f(end)-f(1)
    DZ=1-1/end
    rbulk=mp.sqrt(DT*DT-DZ*DZ)
    rbrane=mp.log(end)
    near=rbulk-mp.mpf(".012")
    far=rbulk+mp.mpf(".1")
    # Conformally flat ambient metric: same causal cones as flat
    # Minkowski in (T,x,y,w,z), with positive z along the chord.
    def ambient_margin(r):return DT*DT-DZ*DZ-r*r
    assert rbrane<near<rbulk<far
    assert ambient_margin(near)>0
    assert ambient_margin(far)<0
    # Physical source radius .04 and original photon guard remain distinct.
    assert near-rbrane-mp.mpf(".04")>0
    return dict(status="PASS",
      original_bulk_metric="z^-2 diag(-1,1,1,1,1)",
      embedded_brane="(F(t),x,y,w,z=1/t)",
      induced_metric="diag(-1,t^2,t^2,t^2)",
      physical_signature="one negative, three positive at each t>0",
      brane_null_reach=str(rbrane),
      ambient_endpoint_null_reach=str(rbulk),
      bulk_minus_intrinsic=str(rbulk-rbrane),
      original_near_receiver=str(near),
      original_far_receiver=str(far),
      near_spacelike_on_brane=bool(near>rbrane),
      near_timelike_in_ambient=bool(ambient_margin(near)>0),
      far_spacelike_in_ambient=bool(ambient_margin(far)<0),
      near_ambient_margin_squared=str(ambient_margin(near)),
      far_ambient_margin_squared=str(ambient_margin(far)),
      note="Exact induced metric and numerical t=12 causal location. No physical wave arrival, causal source coupling, 3+1 emergence from finite histories, or strong trace.")
if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
