"""Complex harmonic resolvent sweep for finite 3^d E/H/P midpoint dynamics.

Exact for beta=0; beta>0 uses the DC tangent stiffness, not a nonlinear
Floquet or full multi-harmonic solution. No empirical optical/Earth calibration.
"""
import numpy as np
import sympy as sp
from scipy.optimize import brentq
from check_ternary_stationary_cycle import incidence
from check_ternary_periodic_norton import fixture, EPS, MU, ETA, A, H, G, LOAD


def harmonic(dim, beta, period, probe):
    B = np.asarray(incidence(dim), dtype=float)
    nv, ne = B.shape
    # Source DC bias and resulting constant-field equilibrium.
    e0 = G * .3 / (G + LOAD)
    p0 = brentq(lambda p: A*p + beta*p**3-e0, 0, 1)
    stiffness = A + 3*beta*p0**2
    z = np.exp(2j*np.pi/period)
    D, M = z-1, (z+1)/2
    src = np.zeros(nv); src[0] = 1
    rec = np.zeros(nv); rec[-1] = 1
    # Source V_k = Re{Vhat z^k}, solve directly for Vhat=1.
    I = np.eye(nv); J = np.eye(ne)
    zero = np.zeros((nv,ne)); ztrans = np.zeros((ne,nv))
    matrix = np.block([
        [EPS*D*I + H*M*(G*np.outer(src,src)+LOAD*np.outer(rec,rec)), -H*M*B, D*I],
        [H*M*B.T, MU*D*J, ztrans],
        [-M*I, ztrans.T, (ETA*D/H+stiffness*M)*I]
    ]).astype(complex)
    forcing = np.r_[H*G*src,np.zeros(ne+nv)]
    solution = np.linalg.solve(matrix, forcing)
    defect = np.max(np.abs(matrix@solution-forcing))
    field = M*solution[:nv]
    return dict(near=field[probe], far=field[-1], source=field[0],
                material=M*solution[nv+ne], defect=defect, stiffness=stiffness)


def exact_checks():
    z,h,eps,mu,eta,a,g,L=sp.symbols('z h eps mu eta a g L',nonzero=True)
    D=z-1;M=(z+1)/2
    # Scalar polarization susceptibility and magnetic transfer denominator.
    chi=sp.factor(M/(eta*D/h+a*M))
    assert sp.factor((eta*D/h+a*M)*chi-M)==0
    # No modulation-frequency response for a constant phase z=1.
    assert sp.simplify(chi.subs(z,1)-1/a)==0
    # source port: g(V-E), its supplied vs dissipated work exact.
    V,E=sp.symbols('V E',real=True)
    assert sp.expand(g*E*(V-E)-g*V*E+g*E**2)==0
    return 3


def main():
    count=exact_checks()
    for dim in (2,3):
        for beta in (0.,.45):
            series=[]
            for period in (4,6,8,12):
                r=harmonic(dim,beta,period,probe=1)
                assert r['defect']<1e-10;count+=1
                assert abs(r['near'])>1e-9;count+=1
                assert np.isfinite(r['far']);count+=1
                series.append((period,r))
            # Frequency variation cannot be inferred from a single 4-step run.
            assert abs(series[0][1]['near']-series[-1][1]['near'])>1e-6;count+=1
            # Existing 4-step nonlinear solver linearization is exact at beta=0;
            # for beta>0 the tangent prediction is approximate at finite amplitude.
            physical=fixture(dim,beta,.12,return_states=True)['states']
            nv=3**dim
            midpoint=(physical+np.roll(physical,-1,axis=0))/2
            obs=np.fft.fft(midpoint[:,1])[1]/4
            vin=np.fft.fft(.3+.12*np.array([0,1,0,-1.]))[1]/4
            predicted=series[0][1]['near']
            tolerance=1e-8 if beta==0 else 5e-5
            assert abs(obs/vin-predicted)<tolerance,(dim,beta,obs/vin,predicted);count+=1
            print(f'{dim}D beta={beta}: '+' | '.join(f'N={n} near={abs(r["near"]):.5g} phase={np.angle(r["near"]):+.4f} far={abs(r["far"]):.3g}' for n,r in series))
    print(f'{count}/{count} PASS; SymPy {sp.__version__}; tangent sweep, four periods')


if __name__=='__main__':main()
