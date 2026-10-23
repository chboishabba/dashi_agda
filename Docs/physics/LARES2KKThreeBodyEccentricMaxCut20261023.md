# Eccentric boosted-Kerr KK nodal dynamics and three-body reuse (2026-10-23)

## Existing owners inspected
- `DASHI/Physics/ThreeBody/State.agda`, `Step.agda`, `Energy.agda`, `Bridge.agda`, `PredictiveBoundary.agda` under master.
- `ThreeBodyStep` carries an abstract operator; `ThreeBodyEnergyAction` packages local energy/action; `ThreeBodyBoundaryDynamics` carries state, regime, admissible path and prediction surfaces. It explicitly denies a global solver claim.
- Reuse this conceptual decomposition for perturbing gravitational orbit models; it is **not** an already-verified geodesic integrator and does not provide ready-made continuous phase-space equations.

## Exact static metric model
For q=sinh²(alpha), F=1-2M/r, H=1+2Mq/r, A=F/sqrt(H), B=sqrt(H)/F, C=r²sqrt(H):
`E²=A(r)*(1+L²/C(r))+A(r)*p_r²/B(r)` for timelike geodesics. At turning points rp,ra:
`L²=(A(ra)-A(rp))/(A(rp)/C(rp)-A(ra)/C(ra))` and `E²=A(rp)*(1+L²/C(rp))`.
Coordinate-time measure `dt/dr = E/A sqrt(B/(E²/A-1-L²/C))`.
For linear-in-spin angular momentum J, a secular node observable at fixed background actions is
`<2J/(r³H)>_t` averaged with **the KK static** radial geodesic time measure, not a Kepler substitute.

## Numerical high precision
`scripts/check_kk_eccentric_geodesic.py` uses 60 decimal-digit mpmath arithmetic, 80-point Gaussian quadrature, and endpoint-regularizing substitution `r=rp+(ra-rp)sin²(chi)`. For fixed seed M and coordinate turning points:
- a=7820km,e=.001, alpha=.3: delta -1.051845835e-10; alpha=1: -1.566549274e-9.
- a=12270km,e=.0045, alpha=.3: -6.703695543e-11; alpha=1: -9.984038572e-10.
Zero boost matches GR. `delta` is relative to q=0 static geodesic and is not an observational constraint or fixed-ADM-mass comparison.
At these precision scales binary float subtraction of turning point quantities suffered cancellation, so high-precision arithmetic was essential.

## Residuals / promotion boundary
- Agda kernel proof of continuous geodesic mechanics, positivity/bound-orbit premises and averaging integrals remains unproved.
- Physical Earth rotating interior matching, KK charge/radion coupling, fixed observable coordinate-independent comparison, geodesic deviation vs real satellite laser-ranging and nuisance covariances are open.
- Three-body multi-source perturbations can later be adapted as a force/step consumer, but its current abstract carrier does not resolve physical source or calibration.
- PR #1239 pp-wave remains incompatible with an isolated rotating Earth; the boosted black string is also not an Earth solution.

Acceptance: `python3 scripts/check_kk_eccentric_geodesic.py`. Source: own code and prior PR #1241 boosted-Kerr construction.
