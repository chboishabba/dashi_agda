import sympy as s
R=s.Rational
# Original mode-3 SBP2 constraint, energy spectral slice; boundary lift.
v=-R(3,5); b=R(3,4); a=1+v; c=1-v
count=0
for n in (3,4,5,8):
 for h in (R(1,16),R(1,32)):
  I=s.eye(n); D=s.zeros(n); D[0,0]=-1; D[0,1]=1; D[-1,-2]=-1; D[-1,-1]=1
  for j in range(1,n-1): D[j,j-1]=-R(1,2); D[j,j+1]=R(1,2)
  D/=h; e=I[0,:]; f=I[-1,:]; z=s.zeros(1,n)
  C=(-D).row_join(I/2).row_join(-I/2).col_join(z.row_join(a*e).row_join(-c*e)).col_join(z.row_join(f).row_join(z))
  E=s.zeros(n+2,2); E[n,0]=1; E[n+1,1]=1
  L=s.zeros(3*n,2); L[n,0]=L[2*n,0]=1/(2*v); L[2*n-1,1]=L[3*n-1,1]=1
  assert C*L==E; count+=1
  W=s.diag(*[(h/2 if j in (0,n-1) else h)/(b+j*h)**3 for j in range(n)])
  for lam in (R(1),R(22)):
   H=s.diag(lam*W,a*W/2,c*W/2); B=H.inv()*C.T; J=B*(C*B).inv(); T=J*E
   assert C*T==E; count+=1
   assert T.T*H*(L-T)==s.zeros(2); count+=1
   cap=s.diag(h/(8*b**3*v**2),h/(2*(b+(n-1)*h)**3))
   assert L.T*H*L==cap; count+=1
   assert cap-T.T*H*T==(L-T).T*H*(L-T); count+=1
   # Moving wall derivative functional: Cdot X = vd*(P0+M0).
   row=s.zeros(1,3*n); row[0,n]=row[0,2*n]=1
   assert (row*H.inv()*row.T)[0]==2/W[0,0]*(1/a+1/c); count+=1
   # Nonlocality: wall lift changes U at the distant normal endpoint.
   assert T[n-1,0]!=0; count+=1
print(f'{count}/{count} exact assertions PASS')
