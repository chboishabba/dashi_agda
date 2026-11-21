"""Finite BIDI admission with separately observed controller port.

Uses the committed 3^d open Cartesian incidence and midpoint field law.
This is an inverse-identification fixture, not physical natural-power evidence.
"""
import numpy as np
from scipy.optimize import root
from check_ternary_multistep_bidi import incidence, grad, storage, evolve


def reconstruct(dim, beta, known_controller=True):
    B = incidence(dim)
    nv, ne = B.shape
    dt = 0.11
    E0 = np.linspace(-.2, .3, nv)
    H0 = np.linspace(.1, -.1, ne)
    P0 = np.linspace(-.03, .04, nv)
    a0 = np.full(nv, 4.0)
    a1 = a0.copy(); a1[nv//2] += .07
    natural = np.zeros(nv); natural[0] = .07
    controller = np.zeros(nv); controller[nv//2] = -.03

    def residual(z):
        E1, H1, P1 = np.split(z, [nv, nv+ne])
        Em = (E0 + E1)/2; Hm = (H0+H1)/2
        return np.r_[.85*(E1-E0)+(P1-P0)-dt*(B@Hm+natural+controller),
                     .9*(H1-H0)+dt*(B.T@Em),
                     .35*(P1-P0)/dt+grad(P0,P1,a0,a1,beta)-Em]

    sol = root(residual, np.r_[E0,H0,P0], tol=1e-11)
    assert np.linalg.norm(residual(sol.x), ord=np.inf) < 1e-10
    E1,H1,P1 = np.split(sol.x,[nv,nv+ne]); Em=(E0+E1)/2; Hm=(H0+H1)/2
    total = (.85*(E1-E0)+(P1-P0))/dt-B@Hm
    assert np.max(np.abs(total-natural-controller)) < 1e-10
    if known_controller:
        recovered_natural = total-controller
        assert np.max(np.abs(recovered_natural-natural)) < 1e-10
        assert np.count_nonzero(np.abs(recovered_natural)>1e-9) == 1
    else:
        # Same field under distinct decompositions: a non-identification witness.
        shift = np.zeros(nv); shift[0] = .02
        assert np.max(np.abs(total-(natural+shift)-(controller-shift))) < 1e-10
    # Signed boundary accounting must be preserved under source-split ambiguity.
    wn=dt*np.dot(Em,natural); wc=dt*np.dot(Em,controller)
    wm=np.dot(a1-a0,P0*P0+P1*P1)/4
    loss=.35*np.dot(P1-P0,P1-P0)/dt
    du=storage(E1,H1,P1,a1,beta)-storage(E0,H0,P0,a0,beta)
    assert abs(du-wn-wc-wm+loss) < 1e-10
    return max(abs(du-wn-wc-wm+loss),np.linalg.norm(residual(sol.x),ord=np.inf))


def main():
    tests=0
    for dim in (2,3):
        for beta in (0.,.45):
            for known in (False,True):
                value=reconstruct(dim,beta,known)
                assert value < 1e-10
                tests += 1
                print(f'dim={dim} beta={beta} known_controller={known} residual={value:.3g}')
    for dim in (2,3):
        for beta in (0.,.45):
            result = evolve(dim,beta)
            assert (result['max_ledger_error'] if isinstance(result,dict) else result) < 1e-10
            tests += 1
    print(f'{tests}/{tests} configurations PASS (8 inverse fixtures; 4 committed multi-step trajectories)')

if __name__ == '__main__':
    main()
