# Boosted rotating KK exact geometry and LARES-2 nodal proxy (2026-10-23)

## New constructive result
Starting with Kerr × flat line (locally Ricci-flat), perform a constant Lorentz boost mixing Kerr time t and the fifth coordinate w, then reduce along the boosted spacelike Killing coordinate W. Denote q=sinh²(alpha), c=cosh(alpha), f=2Mr/(r²+a² cos²(theta)), and B=g^Kerr_(t phi)=-2Mar sin²(theta)/(r²+a² cos²(theta)). The reduced Einstein-frame metric obeys

- H=1+q f;
- g^E_(T phi)=c B/sqrt(H);
- g^E_(TT)=(-1+f)/sqrt(H);
- M4=M(1+q/2), J4=Ma c (leading asymptotic ADM coefficients in geometric units).

The symbolic identities and O(r^-2) spin-term expansion are tested in `scripts/check_boosted_kerr_kk.py`. The vacuum claim relies on the standard Kerr Ricci-flat theorem and a coordinate boost, not an independently computed 5D Ricci tensor in this fixture. For compact circle quotient the global Killing identification and spacelike domain must be specified. The reduction has nonzero Kaluza-Klein electric gauge potential and radion for alpha !=0.

**At fixed physical J4, the leading O(1/r) gravitomagnetic coefficient equals Kerr's**, so leading-order Lense–Thirring does not discriminate this realization.

## Weak-field spin-orbit nodal proxy
For the selected leading spin-orbit term and unperturbed Kepler ellipse, the ratio is
`R=<r^-3 / sqrt(1+2M q/r)>_time / <r^-3>_time`.
Expanding at weak field gives
`R=1-(M q/a_orbit)(1+e²/2)/(1-e²)+O((M q/a_orbit)^2)`.
Numerical quadrature in `scripts/check_boosted_kerr_nodal_proxy.py` confirms this and obtains delta~-4.9922e-10 for alpha=1, 12270 km illustrative LARES-2-class orbit. This is a **selected spin-orbit proxy**: physical 4D nonspin potentials, charge/matter coupling and other orbital effects are NOT held consistent in the reduced dynamics. The spin-independent KK corrections can be larger and modify orbital elements; no full 4D geodesic perturbation or satellite residual is claimed.

## Important limits / empirical promotion firewall
1. Kerr x S1 is a black-hole exterior, NOT an Earth interior solution.
2. A boost of a compactified product must define a new (possibly helical) global identification; reduction is locally meaningful, globally model-dependent.
3. Boosted KK solution is generically charged/dilatonic. Earth net KK charge is not specified or justified.
4. The `~10^-10` ratio is not a published experimental bound or observed nodal residual. No bound on alpha follows.
5. A second independent Earth-compatible 5D solution and consistent physical metric/coupling are needed before comparing with Ciufolini et al. (Nature 2026, DOI 10.1038/s41586-026-10715-0).

## Run
```bash
python3 scripts/check_lares2_kk_frame_dragging.py
python3 scripts/check_lares2_signed_combination.py
python3 scripts/check_boosted_kerr_kk.py
python3 scripts/check_boosted_kerr_nodal_proxy.py
```
Exact GitHub-head execution and Agda kernel checking not yet observed. Local independently executed Python versions of the last two scripts passed.
