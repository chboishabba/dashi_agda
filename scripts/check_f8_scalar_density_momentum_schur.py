"""F8 W1/W2 scalar density-momentum reverse weld and boundary Schur socket.
Consumes original scalar_reverse_bianchi and scalar_master_flux_weld identities.
No independent pressure law, no k=0 inversion, no automatic energy gap.
"""
import sympy as s

def exact():
    b,k=s.symbols('b k',positive=True);B=s.sqrt(1+b*b);q=s.I*k*b
    K,w=s.symbols('K w',positive=True)
    F,G,Z,D,Fn,Zn,f,ft,u,ut,v,V,jx,jy,jm=s.symbols('F G Z D Fn Zn f ft u ut v V jx jy jm')
    r=Z+F/3
    l=-2*B**2*(F-2*r)+2*b*b*(G-2*r)-2*B*b*D
    W=2*B*b*(F-G)+(B*B+b*b)*D
    lam=-2*b*b*(F-2*r)+2*B**2*(G-2*r)-2*B*b*D
    rho=s.symbols('rho')  # independent physical density; constitutive law remains its own equation
    rhog=b*b*f-B*lam/2-b*W-Zn-Fn/3-b*ft+jy
    diff=3*Zn-k*k*b*b*f+jx-jy
    P=w*V+K*q*u
    mix=q*(W/2+ft-b*f)-3*P-jm
    A=rho+B*(G-2*r)-b*D/2+Fn/3-(jx+2*jy)/3
    # Sum of actual Israel residual rows: density, anisotropic, mixed.
    combined=q*(k*k*b*b*f/3+A)+b*(3*P+jm)
    assert s.simplify(combined-q*(rho-rhog)+q*diff/3+b*mix)==0
    # If three physical rows vanish, f is obtained from density and momentum.
    reconstructed=-3*(A+b*(3*P+jm)/q)/(k*k*b*b)
    assert s.simplify(combined.subs(f,reconstructed))==0
    # The boundary master cross term loses its apparent k² growth on-shell.
    t=1/b;j=s.symbols('j')
    raw=(t*k*k*f/3-t**3*j/3)*Z
    Q=A+(3*P+jm)/(s.I*k)+j/3
    assert s.simplify(raw.subs(f,reconstructed)+t**3*Z*Q)==0
    # No k=0 quotient: multiplied relation has finite, nontrivial limit.
    assert s.simplify(combined.subs(k,0)-b*(3*w*V+jm))==0
    # Positive block-Schur form: actual cross coefficient t³, unknown gap eta.
    lamk,eta,z0,z1=s.symbols('lambda eta z0 z1',positive=True)
    energy=lamk*z0*z0/2+eta*z1*z1/(2*lamk)-t**3*z0*z1
    square=lamk*(z0-t**3*z1/lamk)**2/2+(eta-t**6)*z1*z1/(2*lamk)
    assert s.expand(energy-square)==0
    # Exact modal high-frequency weights of geometry and momentum reconstructions.
    assert s.simplify(k**4*(3/(k*k*b*b))**2-9/b**4)==0
    assert s.simplify(k**6*(3*b/(q*k*k*b*b))**2+9/b**4)==0
    # Negative control: abstract Schur socket alone is not a physical gap witness.
    assert s.simplify(energy.subs({lamk:1,eta:t**6/2,z0:t**3*z1}))==-t**6*z1*z1/4
    print('9 grouped symbolic checks PASS: density-momentum reverse weld, zero mode, master flux, Schur negative control')

if __name__=='__main__':exact()
