#!/usr/bin/env python3
"""S5 conditional two-mode dipole energy ledger; not Filsinger hardware evidence."""
import sympy as s
ar, ai, br, bi, fr, fi, xr, xi, wd, wa, ga, gb, kr, kl, g, C, v, bleed, spark = s.symbols('ar ai br bi fr fi xr xi wd wa ga gb kr kl g C v bleed spark', real=True)
assertions = 0

def check(expr):
    global assertions
    assert s.simplify(expr) == 0, s.factor(expr)
    assertions += 1

# Complex amplitudes a and b use real/imaginary coordinates.
# da=(i*wd-ga)*a + i*g*b + f
# db=(i*wa-gb-kr-kl)*b + i*g*a + sqrt(2kr)*splus
# x=sqrt(2kr)*splus. Energy normalization E=|a|^2+|b|^2.
da_r = -wd*ai-ga*ar-g*bi+fr
da_i = wd*ar-ga*ai+g*br+fi
db_r = -wa*bi-(gb+kr+kl)*br-g*ai+xr
db_i = wa*br-(gb+kr+kl)*bi+g*ar+xi
Eab_dot = 2*(ar*da_r+ai*da_i+br*db_r+bi*db_i)
A=ar**2+ai**2
B=br**2+bi**2
Pdriver=2*(ar*fr+ai*fi)
Pincident_overlap=2*(br*xr+bi*xi)
check(Eab_dot-(Pdriver+Pincident_overlap-2*ga*A-2*(gb+kr+kl)*B))

# Scattering boundary: sminus=-splus+sqrt(2kr)*b
t=s.symbols('t',positive=True,real=True) # normalized sqrt(2kr)
sp_r,sp_i=s.symbols('sp_r sp_i',real=True)
Pout=(-sp_r+t*br)**2+(-sp_i+t*bi)**2
Pin=sp_r**2+sp_i**2
check(s.expand(Pin-Pout-(2*t*(br*sp_r+bi*sp_i)-2*kr*B)).subs(t**2,2*kr))

# Ideal abstract load-power transfer to bank, not diode constitutive law.
# Bank E=0.5*C*v**2; C*v*dv/dt = Pload-Pbleed-Pspark.
# At v=0, use energy-state form to avoid a spurious division by v.
Pload=2*kl*B
Pbleed=bleed*v**2
Pspark=spark*v**2
Ebank_dot=Pload-Pbleed-Pspark
check(s.expand((Eab_dot+Ebank_dot-Pdriver+2*ga*A+2*gb*B+Pbleed+Pspark-(Pin-Pout)).subs({xr:t*sp_r,xi:t*sp_i})).subs(t**2,2*kr))

zero={z:0 for z in [ar,ai,br,bi,fr,fi,xr,xi,v]}
for q in (da_r,da_i,db_r,db_i,Eab_dot,Ebank_dot,Pdriver,Pload,Pspark):
    check(q.subs(zero))
check(s.diff(Eab_dot,g))
check(s.diff(Eab_dot,wd))
check(s.diff(Eab_dot,wa))
print(f'S5 exact symbolic acceptance: {assertions}/{assertions} PASS (SymPy {s.__version__})')
