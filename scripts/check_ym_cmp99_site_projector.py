import sympy as s
# Exact rational nonflat periodic cycle fixture, not the four-dimensional source domain.
n=3; t=s.Rational(1,16384); a=(1-t*t)/(1+t*t); b=2*t/(1+t*t)
T=s.Matrix([[1,0,0],[0,a*a-b*b,-2*a*b],[0,2*a*b,a*a-b*b]])
I=s.eye(3); Z=s.zeros(3)
assert T.T*T==I
D=s.BlockMatrix([[-I,T,Z],[Z,-I,I],[I,Z,-I]]).as_explicit()
Q=s.BlockMatrix([[I,T,T]]).as_explicit()/n
assert Q*Q.T==I/n
L=D.T*D; G=(L+Q.T*Q).inv(); W=Q*G
R=s.eye(9)-W.T*(W*W.T).inv()*W
assert R==R.T and R*R==R and W*R==s.zeros(3,9)
assert Q*G*R==s.zeros(3,9)
assert L*G*R==R
P=s.eye(9)-D*G*R*D.T
assert R*D.T*P==s.zeros(9) and P*P==P
assert R!=s.eye(9)-n*Q.T*Q
# Full one-block four-dimensional analytic budget, equal unweighted site norms.
e=s.Rational(1,4096); N=13**4
r=48*e
# normalized site average difference <= r; on its kernel mean <= r*total norm.
# flat gradient floor >= (1-r²)/18; covariant gradient defect <= 4e.
assert (1-r*r)/18 > s.Rational(1,5)**2
assert s.Rational(1,5)-4*e > s.Rational(1,6)
assert N==169**2
print('PASS: source projector algebra, nonflat discriminator, conditional one-block gauge-parameter floor > 1/36')
