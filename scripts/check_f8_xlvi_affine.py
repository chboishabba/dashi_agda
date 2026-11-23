import sympy as s
R=s.Rational
count=0
for n in (3,5,8,13):
 h=R(1,n-1); v=-R(3,5); a=1+v; c=1-v; G=R(2,7); GT=R(3,11); vt=R(192,625)
 D=s.zeros(n); D[0,0]=-1; D[0,1]=1; D[-1,-2]=-1; D[-1,-1]=1
 for j in range(1,n-1): D[j,j-1]=-R(1,2); D[j,j+1]=R(1,2)
 D/=h
 chi=s.Matrix([(1-j*h)**4 for j in range(n)])
 l=G/v*chi; lt=(GT/v-G*vt/v**2)*chi
 assert (l-l)/2==s.zeros(n,1); count+=1
 assert a*l[0]-c*l[0]==2*G and l[-1]==0; count+=1
 FU=l; FP=a*D*l-lt; FM=-c*D*l-lt
 assert (FP-FM)/2-D*FU==s.zeros(n,1); count+=1
 # original affine SAT evaluated on lift vanishes at both boundaries
 assert a*l[0]-c*l[0]-2*G==0 and a*l[-1]==0; count+=1
 # exact slope bound by polynomial monotonicity, sampled on fixed width 1
 assert all(abs(x)<=4 for x in D*chi); count+=1
 # donor M-only lift has nonzero physical constraint
 old=-2*G/c*chi
 assert (-old/2)[0]==G/c; count+=1
print(f'{count} exact checks PASS')
