"""Exact-balance constant-forcing periodic receiver states on open 3^d grids.

DC steady states are period-one orbits, not evidence for a measured source.
All forcing and material coefficients are synthetic, dimensionless inputs.
"""
from itertools import product
import numpy as np
from scipy.optimize import root

DT, EPS, MU, ETA, A, LOAD = .11, .85, .9, .35, 4., .18


def incidence(dim):
    vertices = list(product(range(3), repeat=dim))
    index = {v: i for i, v in enumerate(vertices)}
    edges = [(p, axis) for axis in range(dim)
             for p in product(*(range(2 if j == axis else 3) for j in range(dim)))]
    B = np.zeros((len(vertices), len(edges)))
    for k, (p, axis) in enumerate(edges):
        q = list(p); q[axis] += 1
        B[index[p], k] = -1
        B[index[tuple(q)], k] = 1
    return B


def energy(E, H, P, beta):
    return (EPS*np.dot(E, E) + MU*np.dot(H, H) + A*np.dot(P, P))/2 + beta*np.sum(P**4)/4


def material_gradient(P0, P1, beta):
    return A*(P0+P1)/2 + beta*(P0+P1)*(P0*P0+P1*P1)/4


def fixture(dim, beta, natural_amplitude, controller_amplitude, steps=12):
    B = incidence(dim)
    n, m = B.shape
    jn = np.zeros(n); jn[0] = natural_amplitude
    jc = np.zeros(n); jc[-1] = controller_amplitude
    r = np.zeros(n); r[-1] = 1.
    # From B.T E=0 on a connected grid: E=e*ones.
    # Summing the electric equations gives LOAD*e=sum(jn+jc).
    e = float(np.sum(jn+jc)/LOAD)
    E = np.full(n, e)
    p = float(root(lambda z: A*z + beta*z**3 - e, np.array([e/A])).x[0])
    P = np.full(n, p)
    flux_rhs = LOAD*e*r - jn - jc
    H = np.linalg.lstsq(B, flux_rhs, rcond=None)[0]
    assert np.max(np.abs(B@H-flux_rhs)) < 1e-11
    assert np.max(np.abs(B.T@E)) < 1e-11
    assert abs(A*p+beta*p**3-e) < 1e-11
    E0, H0, P0 = E.copy(), H.copy(), P.copy()
    start = energy(E,H,P,beta)
    works = np.zeros(5)  # natural,controller,receiver,relaxation,storage
    maximum_residual = 0.
    for _ in range(steps):
        def residual(z):
            E1, H1, P1 = np.split(z, [n, n+m])
            Em=(E+E1)/2; Hm=(H+H1)/2
            return np.r_[EPS*(E1-E)+(P1-P)-DT*(B@Hm+jn+jc-LOAD*Em*r),
                         MU*(H1-H)+DT*B.T@Em,
                         ETA*(P1-P)/DT+material_gradient(P,P1,beta)-Em]
        solved = root(residual, np.r_[E,H,P], tol=1e-11)
        rr = float(np.max(np.abs(residual(solved.x))))
        assert rr < 1e-10, (dim,beta,rr)
        E1,H1,P1 = np.split(solved.x, [n,n+m])
        Em=(E+E1)/2; dp=P1-P
        wn=DT*np.dot(Em,jn)
        wc=DT*np.dot(Em,jc)
        useful=DT*LOAD*Em[-1]**2
        relaxation=ETA*np.dot(dp,dp)/DT
        du=energy(E1,H1,P1,beta)-energy(E,H,P,beta)
        ledger=du-wn-wc+useful+relaxation
        assert abs(ledger)<1e-10
        works+=np.array([wn,wc,useful,relaxation,du])
        maximum_residual=max(maximum_residual, rr, abs(ledger))
        E,H,P=E1,H1,P1
    reset=float(np.linalg.norm(np.r_[E-E0,H-H0,P-P0]))
    assert reset<1e-9
    assert abs(works[4]-(energy(E,H,P,beta)-start))<1e-9
    assert abs(works[4]-works[0]-works[1]+works[2]+works[3])<1e-9
    assert works[2]>=0 and works[3]>=0
    assert abs(works[2]-(works[0]+works[1]))<1e-9
    if natural_amplitude==controller_amplitude==0:
        assert abs(works[2])<1e-13
    if natural_amplitude==0:
        assert abs(works[0])<1e-13
    if controller_amplitude==0:
        assert abs(works[1])<1e-13
    return dict(dim=dim, beta=beta, natural_amplitude=natural_amplitude,
                controller_amplitude=controller_amplitude, receiver_work=works[2],
                natural_work=works[0], controller_work=works[1],
                storage_delta=works[4], reset=reset, residual=maximum_residual)


def main():
    count=0
    for dim in (2,3):
        for beta in (0.,.45):
            for natural,controller in ((.07,0.),(.07,.02),(0.,.02),(0.,0.)):
                result=fixture(dim,beta,natural,controller)
                assert result['reset']<1e-9
                assert result['residual']<1e-10
                assert abs(result['receiver_work']-result['natural_work']-result['controller_work'])<1e-9
                count+=3
                print(result)
    print(f'{count}/{count} PASS; 16 equilibrium fixtures, 192 midpoint steps')


if __name__=='__main__':
    main()
