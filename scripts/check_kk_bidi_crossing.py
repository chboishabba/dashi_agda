import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
T=27.5
Gkk=2.9851955e-10/2
# finite linear sweep delta/G from -10 to +10; pure diabatic initial state
# equal amplitude damping gamma/2, norm loss exp(-gamma*T)
def run(G, ratio=10, gamma=0):
    def rhs(u,z):
        d=ratio*G*(2*u-1)
        return -1j*T*np.array([d*z[0]/2+G*z[1],G*z[0]-d*z[1]/2])-gamma*T*z/2
    z=solve_ivp(rhs,(0,1),np.array([1+0j,0j]),rtol=2e-10,atol=2e-12).y[:,-1]
    assert abs(np.vdot(z,z).real-np.exp(-gamma*T))<1e-7
    return abs(z[1])**2
for p in [.9,.99,.999]:
    G=10*np.log(1/(1-p))/(np.pi*T)
    print('LZ asymptotic design',p,G,'finite',run(G),'damped',run(G,gamma=.001))
print('KK finite sweep',run(Gkk), 'speed bound',np.sin(Gkk*T)**2)
print('exact resonant pulse G',np.pi/(2*T),'loss for gamma=.001',np.exp(-.001*T))
# Find first finite-sweep 99% crossing on declared grid, not global optimizer
xs=np.linspace(.001,1.5,250); ys=[run(g) for g in xs]
for a,b,pa,pb in zip(xs[:-1],xs[1:],ys[:-1],ys[1:]):
    if pa<.99<=pb:
        root=brentq(lambda g:run(g)-.99,a,b);print('first grid-bracketed finite 99%',root,run(root));break
# Two-level mean-field block: derivative in eigenbasis perpendicular to H
xi,D,dx,dD=s.symbols('xi D dx dD',real=True); E2=xi**2+D**2
assert s.expand((dx**2+dD**2)*E2-(xi*dx+D*dD)**2-(xi*dD-D*dx)**2)==0
beta=s.symbols('beta',real=True)
assert s.expand((xi*dD-D*dx).subs({dD:beta*D,dx:beta*xi}))==0
print('PASS BCS transverse derivative and common-scaling dark control')
