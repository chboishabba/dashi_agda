# LARES-2 GR/KK observation max-cut: physical core only

## Architecture
W3 means DASHI's internal **W3 accepted empirical authority gate** (NOT W3C, the World Wide Web Consortium). PNF and W3 are NOT dependencies for geodesic dynamics, observables, estimation, or numerical tests. W4's stress-energy boundary can be reused without claiming the DASHI carrier has derived Earth.

Reuse canonical ThreeBody.Step, ThreeBody.Energy and ThreeBody.Bridge as generic dynamical/energy interfaces; they do not solve differential equations automatically. Existing KK PR #1238/#1239 and current #1241 provide the rotating quotient and conditional geodesic construction.

## New executable same-observable synthetic vertical slice
Run `python3 scripts/check_lares2_range_identifiability.py`.
- Earth-spin GR nodal rate for representative circular 12,270 km satellite.
- Cartesian inclined circular orbit with secular orbital-plane rotation; common deterministic satellite geometry.
- Rotating ground-station Cartesian coordinates; instantaneous Euclidean ranges.
- Centered finite-difference sensitivity to dimensionless fractional nodal rate.
- Weighted least squares nuisance residualization via SVD for toy constant range bias, secular range slope, and sidereal periodic term.
- Explicit non-identifiability counterexample when the signal itself is inserted into nuisance span.
- An illustrative boosted-Kerr metric KK delta of order 10^-9, NOT an Earth-justified physical parameter or constraint.

Local preliminary execution: projected Fisher 1.888756e5, toy sigma_delta 2.300976e-3, illustrative alpha=1 delta -9.984039e-10, signal/noise ~4.339045e-7. These are toy inputs; do not compare directly with published LARES-2 inferred covariance.

## Strict unclosed cut
Actual Satellite Laser Ranging is two-way photon propagation and reflection, with time scales, terrestrial/celestial frame transformations, Earth geopotential/tides and stations, precise ephemerides and fit covariance. The script intentionally omits these; it cannot reproduce LARES-2 measurements. The physically relevant KK Earth model also requires matter stress-energy and matching, scalar/gauge charge and satellite coupling. SymPy/NumPy local receipts do not establish Agda kernel results or empirical validation.

## Next exact implementation cut
1. Add geodetic station and Earth-orientation model, solve emission/bounce/reception light-time iteratively.
2. Ingest sourced ILRS records and ICGEM gravity coefficients (checksum, units, epochs).
3. Instantiate real perturbation Jacobian incl. J2/J4, station bias, solar/lunar tides, initial state and covariance; use same nuisance projection for GR/KK.
4. Enforce frame and observable parity in a commuting theorem; introduce optional W3 authority adapter only after primary calculations, never upstream.
5. Test if KK signature remains outside nuisance span under independently calibrated physical parameters.

Attribution: DASHI existing three-body, GR-precision, W4 source and KK modules; standard least-squares projection and orbital dynamics; new synthetic executable test. No claim of novelty of standard mathematics.
