"""Continuous-source reversible HF storage cycle, same ideal modal endpoint.
Two degenerate HF catalyst modes rotate their action without pausing source.
"""
import sympy as S
from solar_steelman_unity import zero,geometry,modal_cycle,rhs
from solar_steelman_hf_catalyst import common_clock,hamiltonian


def two_mode_hamiltonian():
    c,b,d,p,q,cc,bb,dd,pp,qq,chi,k=S.symbols('c b d p q cc bb dd pp qq chi k')
    action=p*pp+q*qq;K=cc*b*d-c*bb*dd
    H=-S.I*chi*action*K+S.I*k*(qq*p-pp*q)
    pairs=((c,cc),(b,bb),(d,dd),(p,pp),(q,qq))
    f=[S.expand(-S.I*S.diff(H,v)) for u,v in pairs]
    fc=[S.expand(S.I*S.diff(H,u)) for u,v in pairs]
    assert zero(f[3]+chi*p*K+k*q) and zero(f[4]+chi*q*K-k*p)
    assert S.expand(f[3]*pp+p*fc[3]+f[4]*qq+q*fc[4])==0
    assert S.expand(f[0]*cc+c*fc[0]+(f[1]*bb+b*fc[1]+f[2]*dd+d*fc[2])/2)==0
    return H


def continuous():
    F,_=geometry();x,M=modal_cycle(F);t=S.symbols('t',real=True)
    p=S.cos(2*S.pi*t);q=S.sin(2*S.pi*t);chi=S.sqrt(2);k=2*S.pi
    action=S.trigsimp(p*p+q*q);assert action==1
    assert zero(rhs(x,1,g=chi*action))
    K=S.conjugate(x[1])*x[2]*x[3]-x[1]*S.conjugate(x[2])*S.conjugate(x[3]);assert zero(K)
    assert zero(S.diff(p,t)+chi*p*K+k*q) and zero(S.diff(q,t)+chi*q*K-k*p)
    z=x.col_join(S.Matrix([p,q]));assert z.subs(t,0)==z.subs(t,1)
    # Common continuously incident unit source, no gated switching windows.
    assert (1-S.sqrt(2)*x[0])**2==0
    useful=(x[2]+x[3])**2/2;dark=(x[2]-x[3])**2/2
    assert S.integrate(useful,(t,0,1))==1 and dark==0
    cycles,ratio=common_clock();store1=ratio*p*p;store2=ratio*q*q
    assert S.trigsimp(store1+store2)==ratio
    assert store1.subs(t,0)==ratio and store2.subs(t,S.Rational(1,4))==ratio
    assert store1.subs(t,1)==ratio and store2.subs(t,1)==0
    # At nominal trajectory the interaction and internal mixing Hamiltonian
    # vanish (real phase lock); the occupied modal energy remains positive.
    # In a fixed-action chart the LF block is the prior Schur map; HF frame
    # rotation and common phase are neutral conserved fibres, not attractors.
    return ratio


def reverse_maintenance(ratio):
    chi,gamma,epsilon=S.symbols('chi gamma epsilon',positive=True)
    store=ratio*S.sqrt(2)/chi
    # Unit normalized cycle; gamma is amplitude damping per normalized time.
    cost=2*gamma*store;bound=epsilon/(2*store)
    assert S.cancel(cost.subs(gamma,bound)-epsilon)==0
    # Physical start-up store and maintenance are distinct. At exact unity
    # and nonzero occupied store, gamma must vanish or be losslessly returned.
    return store,bound


def run():
    hamiltonian();two_mode_hamiltonian();ratio=continuous();store,bound=reverse_maintenance(ratio)
    print('PASS continuous incident unity with two-mode HF store rotation; full HF store transferred and restored',ratio)
    print('Reverse stored energy and maintenance rate ceiling:',store,bound)
    print('PASS exact full nominal phase and state return; fixed-action LF stability, neutral HF fibres; physical tensor and startup/maintenance unadmitted')
if __name__=='__main__':run()
