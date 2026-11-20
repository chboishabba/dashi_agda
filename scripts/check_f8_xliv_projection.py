import sympy as s

# Original mode-3 SBP2 normal derivative, original moving geometry at t=4/3.
# One positive radial-energy spectral parameter; no claim of full spatial replay.
R=s.Rational
v=-R(3,5); b=R(3,4); a=1+v; c=1-v; vd=R(192,625)
# actual dv/dT=t^3/(1+t^2)^2 at t=4/3 = 192/625
assert vd==R(4,3)**3/(1+R(4,3)**2)**2
count=0
for n in range(3,9):
 h=R(1,16); D=s.zeros(n); D[0,0]=-1;D[0,1]=1;D[-1,-2]=-1;D[-1,-1]=1
 for j in range(1,n-1): D[j,j-1]=-R(1,2);D[j,j+1]=R(1,2)
 D/=h; I=s.eye(n); Z=s.zeros(n); e0=I[0,:]; eN=I[-1,:]
 C=(-D).row_join(I/2).row_join(-I/2).col_join(s.zeros(1,n).row_join(a*e0).row_join(-c*e0)).col_join(s.zeros(1,n).row_join(eN).row_join(s.zeros(1,n)))
 Cd=s.zeros(n+2,3*n); Cd[n,n:2*n]=vd*e0; Cd[n,2*n:]=vd*e0
 assert C.rank()==n+2; count+=1
 W=s.diag(*[(h/2 if j in (0,n-1) else h)/(b+j*h)**3 for j in range(n)])
 for lam in (R(1),R(22)):
  H=s.diag(lam*W,a*W/2,c*W/2); B=H.inv()*C.T; K=C*B; J=B*K.inv(); P=s.eye(3*n)-J*C
  assert C*J==s.eye(n+2); assert C*P==s.zeros(n+2,3*n); assert P*P==P; assert P.T*H==H*P; assert P.T*H*P+ (J*C).T*H*(J*C)==H; count+=5
  # Exact original mode-3 homogeneous RHS with radial force -lambda U.
  warp=s.diag(*[-R(3,2)/(b+j*h) for j in range(n)])
  F=Z.row_join(a*I/2).row_join(c*I/2).col_join((-lam*I).row_join(a*D+warp-2*a/h*eN.T*eN).row_join(-warp)).col_join((-lam*I).row_join(warp+2*a/h*e0.T*e0).row_join(-c*D-warp-2*c/h*e0.T*e0))
  M=P*F-J*Cd
  assert C*M+Cd==s.zeros(n+2,3*n); count+=1
  # For every constrained state x=P y, projection correction has zero energy work.
  assert P.T*H*(M-F)*P==s.zeros(3*n); count+=1
  # Affine wall source: Cx=g and moving tangent C xdot=gdot-Cdot x.
  g=s.zeros(n+2,1); g[n]=R(2,7); gd=s.zeros(n+2,1); gd[n]=R(3,11)
  x=J*g; f=F*x; f[n*2]-=2*g[n]/h # original M SAT source, g[n]=2G
  corrected=P*f+J*(gd-Cd*x)
  assert C*x==g; assert C*corrected+Cd*x==gd; count+=2
print(f'{count}/{count} exact rational SymPy checks PASS; finite projection only, not a uniform PDE theorem')
