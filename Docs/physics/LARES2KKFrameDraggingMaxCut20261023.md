# LARES-2 × KK frame-dragging: exact scope and max-cut (2026-10-23)

Reference: Ciufolini et al., *Nature* 655, 332–335 (2026), DOI: 10.1038/s41586-026-10715-0.

## Architecture/attribution
Reuse master-side LiTorrStandardGRRotatingSourceKernelExact.agda (weak-field Lense–Thirring scaling), sibling PR #1238 (5D Einstein–Maxwell/measurement), sibling PR #1239 (5D Ricci-flat null electromagnetic Brinkmann pp waves and radion families), #1235 (alternative-model discriminator), and #1240 (world-model evidence authority). Their existence does **not** establish a same-object Earth-orbit solution.

## Concrete calculations
- Leading weak-field GR nodal rate: dOmega/dt = 2GJ/[c^2 a^3 (1-e^2)^(3/2)].
- Time-average of inverse cubed Kepler radius: <r^-3> = 1/[a^3(1-e^2)^(3/2)]. Independently checked by adaptive eccentric-anomaly quadrature.
- With approximate Earth J=5.86e33 SI: original LARES-class (a=7820 km, e=.001) ~118.47 mas/yr; illustrative LARES-2/LAGEOS-class (a=12270 km, e=.0045) ~30.67 mas/yr. These are **not fitted orbital elements or actual recovered rates**.
- Algebraic synthetic nuisance cancellation: for column sensitivities K and combination weights w, w^T K=0, w^T signal !=0, R=mu w^T signal+w^T epsilon, Var(R)=w^T Sigma w. A SymPy rational example is checked; K is not measured sensitivity.
- Conditional *phenomenological*, not KK-derived, exterior model g_tphi=(1+delta)g_tphi^GR gives nodal scale (1+delta). The Nature abstract reports ~0.1% relative precision; a +/-0.002 two-sigma delta interval is only an illustrative zero-central-residual Gaussian estimate, **not** a published confidence bound.

## Decisive KK distinction
Kerr x S^1 with flat, constant-radius fibre and A=0 is an exact Ricci-flat 5D product. Its 4D nodal precession equals GR's. Thus a 5D vacuum does not imply detectable delta !=0.
The sibling PR #1239 null pp-wave is non-asymptotically flat and not an isolated rotating Earth. Its 5D vacuum status **does not supply a LARES-2 prediction**.
A nontrivial Earth-compatible KK model needs 5D field equations with rotating matter/source and asymptotics, dimensional reduction and identified physical matter metric, a g_tphi solution, geodesic/other force law, and a satellite observation operator.

## Remaining honest obligations
1. Kernel-check mathematical nodal-precession and nuisance-nullspace proofs in an existing verified numeric carrier (avoid Set/String-only labels).
2. Derive leading-order nodal rate from Kerr/weak-field stationary axisymmetric metric, fixing all sign and coordinate conventions.
3. Obtain the actual LARES-2/LAGEOS + GRACE nuisance sensitivities, orbit fits, covariances and systematic corrections from ILRS/GEODYN/ICGEM; replicate published analysis before promoting experimental authority.
4. Supply a nontrivial rotating, Earth-compatible 5D solution with specified matter coupling, or demonstrate a no-go within declared ansatz. Only then infer any physical KK delta.
5. Compare physical deviations across the same observable and do not infer bounds on generic KK from a single nodal ratio.

## Acceptance
```bash
python3 scripts/check_lares2_kk_frame_dragging.py
python3 scripts/check_lares2_signed_combination.py
```
Both scripts are numerical/symbolic fixtures only; no Agda kernel/CI or empirical data reproduction asserted.
