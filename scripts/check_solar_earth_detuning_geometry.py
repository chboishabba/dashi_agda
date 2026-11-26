"""Conditional finite-frequency cold Drude geometry; no physical calibration."""
import json
import itertools
import sympy as s
I=s.I
D,nu=s.symbols('D nu',positive=True,real=True)
a,w,O=s.symbols('a w O',real=True,nonzero=True)
z=D/(nu+I*a)
assert s.cancel(z*s.conjugate(z)-D**2/(nu**2+a**2))==0
assert s.cancel((z+I*D/(2*a))*s.conjugate(z+I*D/(2*a))-D**2/(4*a*a))==0
assert s.cancel(s.re(z)-nu*z*s.conjugate(z)/D)==0
zp=D/(nu+I*(O-w)); zm=D/(nu+I*(-O-w))
assert s.cancel(1/zp-1/zm-2*I*O/D)==0
assert s.cancel((1/zp+1/zm)/2-(nu-I*w)/D)==0
# Rational quasineutral electron and two singly charged ion species: D/|Omega| sums agree.
species=[(s.Rational(60),-30),(s.Rational(1),1),(s.Rational(2),2)]
assert sum(d/om for d,om in species)==0
checks=0; endpoints=0; modes=[]
for freq in map(s.Rational,('0','1/100','1/2','3/2','5','40')):
    for sign in (-1,1):
        det=[sign*om-freq for d,om in species]
        assert all(det)
        P=sum(d/a for (d,om),a in zip(species,det) if a>0)
        N=sum(-d/a for (d,om),a in zip(species,det) if a<0)
        cap=max(P,N); radius=(P+N)/2; center=I*(N-P)/2
        for rates in itertools.product((0,s.Rational(1,10),1,10,100),repeat=3):
            Z=sum(d/(v+I*a) for (d,om),a,v in zip(species,det,rates))
            assert s.simplify(s.expand_complex((Z-center)*s.conjugate(Z-center)))<=radius**2
            assert s.simplify(s.expand_complex(Z*s.conjugate(Z)))<=cap**2
            assert 0<=s.re(Z)<=radius
            checks+=1
        # nu=infinity is a closure point (zero response), not a finite rate.
        for selected in (-1,1):
            Z=sum(d/(I*a) for (d,om),a in zip(species,det) if selected*a>0)
            assert s.simplify(Z*s.conjugate(Z))==(P if selected==1 else N)**2
            endpoints+=1
        # Maximum real response attained at nu=abs(detuning) for each species.
        Z=sum(d/(abs(a)+I*a) for (d,om),a in zip(species,det))
        assert s.re(Z)==radius
        if freq==0: assert cap==2
        modes.append(dict(omega=str(freq),polarization=sign,cap=str(cap)))
# Resonance and DC parallel branch cannot use the detuned circle.
assert s.limit(D/nu,nu,0,dir='+')==s.oo
print(json.dumps(dict(status='CONDITIONAL_DRUDE_DETUNING_GEOMETRY',sympy=s.__version__,symbolic_identities=5,exact_rate_fixtures=checks,closure_endpoints=endpoints,real_maxima=len(modes),modes=modes,physical_admission=False),indent=2))
