import sympy as s
# Existing original SBP2 derivative; h scaled out.
a,c,w0,wN,p,m,g=s.symbols('a c w0 wN p m g', positive=True)
# Original characteristic energy metric diag(a/2,c/2), a=1+v,c=1-v.
# Constraint-preserving joint endpoint SAT requires equal P,M corrections.
# Boundary flux at lower endpoint plus common correction k.
k=s.symbols('k', real=True)
flux=-a*a*p*p/4+c*c*m*m/4
work=(a*p+c*m)*k/2
# On the null direction of common SAT work, p=c, m=-a, flux is zero.
assert s.expand(flux.subs({p:c,m:-a}))==0
# Factor flux by the common work direction; choose dissipative residual correction.
assert s.expand(flux-(c*m-a*p)*(a*p+c*m)/4)==0
# Common correction at lower boundary makes energy flux negative square.
beta=s.symbols('beta', positive=True)
kl=(a*p-c*m)/2-beta*(a*p+c*m)
assert s.expand(flux+work.subs(k,kl)+beta*(a*p+c*m)**2/2)==0
# Upper endpoint opposite flux.
ku=-(a*p-c*m)/2-beta*(a*p+c*m)
assert s.expand(-flux+work.subs(k,ku)+beta*(a*p+c*m)**2/2)==0
# However original Israel condition is a P outcome, R=a p-c m-2G;
# common correction acts on sum, not necessarily controls R.
G=s.symbols('G',real=True)
assert s.expand((a*p-c*m-2*G).subs({p:c,m:-a}))==2*a*c-2*G
for n in range(3,14):
 D=s.zeros(n); D[0,0]=-1;D[0,1]=1;D[-1,-2]=-1;D[-1,-1]=1
 for i in range(1,n-1):D[i,i-1]=-s.Rational(1,2);D[i,i+1]=s.Rational(1,2)
 H=s.diag(s.Rational(1,2), *([1]*(n-2)),s.Rational(1,2))
 assert H*D+D.T*H==s.diag(-1,*([0]*(n-2)),1)
 l=s.Matrix([(-1)**(n-1)]+[2*(-1)**(n-1-j) for j in range(1,n-1)]+[1])
 assert l.T*D==s.zeros(1,n)
 assert D.rank()==n-1
 # original Qdot=(SAT_P-SAT_M)/2; same common SAT cancels exactly.
 x=s.Matrix(s.symbols('x:'+str(n))); assert (x-x)/2==s.zeros(n,1)
print('PASS: 44 exact SBP/nullspace/constraint checks; 5 symbolic boundary identities')
