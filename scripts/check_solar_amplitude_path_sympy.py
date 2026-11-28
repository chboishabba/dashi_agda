"""Exact one-species jet identities; charge balance tested by native multi-species fixture."""
import sympy as S
s=S.symbols('s',positive=True)
# Positive old/new; newborn; both vanish quadratically; extinction boundary.
# Unit signed mass-volume normalization; velocity of birth fixed at -2.
b=-2
cases=[(4,1,2,2,0,1,3),(0,0,0,0,0,9,0),
       (0,0,0,4,1,1,3),(4,4,0,0,-1,3,3)]
for n,r,a,nu,ru,au,v in cases:
    N=n+s*s*nu; R=r+s*s*ru; A=a+s*s*au; M=N-R+A
    Z=S.sqrt(N)*(v+s) if N!=0 else S.Integer(0)
    V=v+s if N!=0 else S.Integer(0)
    out=((N-R)*V+A*b)/S.sqrt(M)
    out0=S.limit(out,s,0,dir='+'); dz=S.limit((out-out0)/s,s,0,dir='+')
    new=n-r+a; newu=nu-ru+au
    if new>0:
        expected=(n-r)/S.sqrt(new) if n>0 else 0
    else:
        expected=((nu-ru)*v+au*b)/S.sqrt(newu)
    assert S.simplify(dz-expected)==0,(dz,expected)
    incoming=A*b*b/2; outgoing=R*V*V/2
    mixing=(N-R)*A*(V-b)**2/(2*M)
    assert S.simplify((out*out-Z*Z)/2-incoming+outgoing+mixing)==0
# Density-linear path has an infinite amplitude slope, quadratic has finite one.
assert S.limit(S.sqrt(s)/s,s,0,dir='+')==S.oo
assert S.limit(S.sqrt(s*s)/s,s,0,dir='+')==1
print('AMPLITUDE_PATH_EXACT_PASS',len(cases))
