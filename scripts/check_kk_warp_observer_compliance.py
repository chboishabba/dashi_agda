"""Original KSW668 moving-warp algebra and backward compliance discriminator.
Donor #1527 head 123eff9204d91e2b1967e9e72d3d68771f27287f.
Weight contrast is NOT a physical tensor observer gain.
"""
import sympy as s
def check():
    v,z,p,m,src=s.symbols('v z p m src', real=True, nonzero=True)
    a=1+v;b=1-v
    assert s.expand(3/(2*z)*(a*p*p-b*m*m)-3/(2*z)*(p*p-m*m)-3*v/(2*z)*(p*p+m*m))==0
    target=(a*p-2*src)/b
    B=-a*p*p/2+b*target**2/2
    assert s.factor(B+src**2/v-a*(v*p-src)**2/(b*v))==0
    x,y,k,h=s.symbols('x y k h',positive=True)
    L=s.diag(k,h); obs=s.Matrix([x,y]); C=(obs.T*L.inv()*obs)[0]; u=L.inv()*obs/C
    assert s.simplify((obs.T*u)[0]-1)==0
    assert s.simplify((u.T*L*u)[0]-1/C)==0
    G=6.67430e-11;g=9.80665;R=.1375;r=.2375;t=(R/r)**2
    D=g*g*r**6/(4*G*R**3); E=D*6*(1-t)**3/(6-3*t+t*t)
    print('PASS bulk cancellation, boundary square, compliance minimizer')
    print('dipole, optimal, gain',D,E,E/2073)
    print('weight ratio at t=12', (1+12*2.01)**3)
if __name__=='__main__':check()
