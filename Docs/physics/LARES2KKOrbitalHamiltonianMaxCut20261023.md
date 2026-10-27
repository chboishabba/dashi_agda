# LARES-2 KK orbital Hamiltonian max-cut (2026-10-23)

## Concrete theorem (linear in spin, conditional model)

Boost a locally Ricci-flat Kerr × fifth-direction product and reduce along the boosted spacelike Killing field. In the neutral Einstein-frame test-particle model, write q=sinh²(alpha), F=1-2M/r, H=1+2Mq/r, A=F/sqrt(H), B=sqrt(H)/F, C=r²sqrt(H). At O(J), the stationary axisymmetric g_(t phi)=-2J sin²(theta)/(r sqrt(H)) and static spherical geometry admit coordinate-time Hamiltonian:

`E= sqrt(A*(1+p_r²/B+L²/C)) + W(r)*Lz + O(J²)`,
`W(r) = -g_(t phi)/g_(phi phi) = 2J/(r³ H)`.

For Delaunay-type node angle conjugate to Lz, holding total L and radial action fixed, secular nodal drift is `<W(r)>_t+O(J²)`, where the time average is over the unperturbed **KK static** radial motion, not arbitrarily a Kepler ellipse. For circular radius r, `Omega_node = 2J/(r³ H)+O(J²)`.

Independent symbolic fixture `scripts/check_kk_nodal_hamiltonian.py` verifies the metric shift, static equatorial circular frequency `Omega_circ²=A'/C'`, Schwarzschild q=0 limit and circular-geodesic E²/L² formulas. Numerical radius samples pass. This is a derived neutral test-particle orbital observable in a **black-hole-type KK exterior**, not an Earth prediction.

## Correct comparison

Asymptotic physical ADM quantities: `M4=M(1+q/2)` and `J4=Ma cosh(alpha)`. Holding source's **measured ADM mass** M4 fixed requires `M=M4/(1+q/2)`; holding coordinate r fixed is not equivalent to fixing circumferential radius `sqrt(C(r))`. The illustrative delta values printed by fixture keep seed M fixed and compare 2J/r³. Recalibrating M4 reduces delta for alpha=1 at 12270km from about -9.984e-10 to about -5.906e-10 at same coordinate radius, but this remains neither an invariant observational comparison nor a full KK terrestrial fit.

## Non-promoting cuts still required

1. For eccentric orbit: evaluate `<W>_t` with radial period and coordinate-time measure computed from `A,B,C` and turning points, including bound-orbit/stability assumptions; Keplerian proxy is not exact.
2. Derive the four-dimensional source and physical test-body coupling from a rotating compactified five-dimensional **Earth-compatible matter** configuration. Vacuum Kerr uplift is not interior matching and cannot establish the Earth's KK scalar/gauge charge.
3. Map model orbit to conventional osculating elements and laser-ranging observables; fit Earth's independent mass/angular momentum and geopotential nuisance coefficients and observed covariances.
4. Agda kernel proof: migrate SymPy identities to typed real-field/matrix identities with exact nonzero/positivity prerequisites. No kernel receipt supplied.
5. No published constraint on boost alpha; Nature (2026) LARES-2 relative uncertainty is not by itself a bound on this theoretical model.

## Run
```bash
python3 scripts/check_kk_nodal_hamiltonian.py
```

Attribution: standard Kerr black string boosted KK construction and Hamiltonian perturbation theory; repo PR #1241 prior reduction work; this round's new conditional orbital theorem and tests.
