"""Published event summary and exact observer-fibre discriminator; no raw radar replay."""
import sympy as s
import json
R=s.Rational
# van Hazendonk et al. 2024 Table 1; seconds and joules, published rounded values.
T=8100; Qj=124*10**11; Qf=73*10**11; Qp=87*10**11
# Two proxies for one EM dissipation term, distinct kinetic deposition.
# Unknowns [top, other signed work, storage change, EM loss, side, basal,
# kinetic deposition, J proxy bias, F proxy bias]. All energy coordinates in TJ.
A=s.Matrix([[1,1,-1,-1,-1,-1,0,0,0],[0,0,0,1,0,0,0,1,0],[0,0,0,1,0,0,0,0,1],[0,0,0,0,0,0,1,0,0]])
y=s.Matrix([0,R('12.4'),R('7.3'),R('8.7')]);b=s.eye(9)[5,:]
assert A.rank()==4 and A.col_join(b).rank()==5
# A common-proxy shift leaves both proxy observations unchanged, and a side/basal trade does too.
u=s.Matrix([0,0,0,1,0,-1,0,-1,-1]);v=s.Matrix([0,0,0,0,1,-1,0,0,0]);assert A*u==A*v==s.zeros(4,1)
# Even granting exact upstream 20 TJ and Q=12.4 TJ (hypothetical), side/basal unresolved.
for side,basal in [(R('7.6'),0),(0,R('7.6'))]:
    x=s.Matrix([20,0,0,R('12.4'),side,basal,R('8.7'),0,R('-5.1')]);assert A*x==y
# LOS velocity is insufficient for vector drift or the quadratic heating norm.
M=s.Matrix([[1,0]]);x=s.Matrix([1,0]);z=s.Matrix([1,2]);assert M*x==M*z and x.dot(x)!=z.dot(z)
# Identical one electric component and identical magnetic magnitude, opposite signed normal Poynting.
E=s.Matrix([1,0,0]);H=s.Matrix([0,1,0]);n=s.Matrix([0,0,1]);assert E.cross(H).dot(n)==1 and E.cross(-H).dot(n)==-1
# Minimum symmetric absolute proxy error for a shared scalar Q, NOT a confidence interval.
delta=R(Qj-Qf,2);mid=R(Qj+Qf,2);assert mid-delta==Qf and mid+delta==Qj
print(json.dumps(dict(status='PUBLISHED_EVENT_SUMMARY_AND_EXACT_NONIDENTIFICATION',sympy=s.__version__,duration_s=T,energy_J=[Qj,Qf,Qp],mean_power_W=[float(R(q,T)) for q in [Qj,Qf,Qp]],proxy_ratio=float(R(Qj,Qf)),min_common_absolute_proxy_error_J=int(delta),minimax_proxy_midpoint_J=int(mid),joule_cube_to_region_extrapolation=float(R(Qj,77*10**8)),observer_rank=A.rank(),rank_with_basal=A.col_join(b).rank(),nullity=len(A.nullspace()),raw_radar_replayed=False,physical_admission=False),indent=2))
