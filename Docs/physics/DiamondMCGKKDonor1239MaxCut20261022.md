# Diamond MCG ↔ KK live donor #1239 — max-cut 2026-10-22

## Confirmed live donor (PR diff read)
PR #1239 `DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda` proves the horizontal one-form additive identity
`theta(dy-kdchi,A+dchi)=theta(dy,A)` given a witnessed abelian additive group.
Its `scripts/check_kaluza_klein_circle_metric.py` tests representative 2+1 metric gauge covariance, determinant and inverse. The source-written result is not a full 4+1 Einstein–Maxwell reduction. The donor's `docs/c3-braid-kk-exact-bridge-round.md` specifies clearance=1 for its linear braid model and a uniform <1/2 perturbation sufficient condition; no identification of its braid with a KK fibre is assumed.

## Consumer implemented in PR #1238
`DASHI/Physics/Measurement/BioEMKaluzaObservationTransportExact.agda` defines a `LocalKKConnection` acceptance interface with a mandatory horizontal-invariance witness. Generic field/readout and frequency-observation invariance follow by congruence. This is theorem-bearing downstream transport and does not copy the donor's additive group proof. It can consume the donor once merged or cherry-picked into the same exact-head branch. No placeholder proof of Einstein equations has been introduced.

## Distinct physical objects
- C3 rotating three-strand braid: finite and piecewise continuous configuration geometry.
- Hopf U(1) bundle: principality, connection curvature and Chern invariants.
- KK 5D circle bundle: metric, fibre coordinate, gauge transformation, geometric reduction.
- Standard 4D Maxwell: electric and magnetic field strength, currents, boundary-value problem.
- Biological source: cardiac/neural currents, volume conduction, uncertain geometry.
- NV centre: electronic spin-1 sensing, optical excitation and measured fluorescence.
- Mitochondrial polariton: candidate spectroscopy/ATP mechanism; no inferred KK dimension.

## Residual closure ranked
1. Merge the actual #1239 donor or carry an explicit Agda import only after the donor definitions are in scope. Construct the `LocalKKConnection` instance from its additive-group `Gauge` module.
2. Prove fibre-to-curvature map is compatible with the Maxwell current-to-field representation and its physical gauge transformations, including unit/normalization conventions.
3. Complete 4+1 metric gluing, Ricci reduction and Maxwell plus scalar field equations; gauge identity alone is insufficient.
4. Add full complex NV response, optical statistical likelihood and experimental calibration.
5. Provide quantitative biological current and tissue forward data, actual uncertainty receipts and paper figure replay.
6. Compare source-specific mitochondrial coupled-mode and optogenetic factorial model against raw data and competing classical mechanisms.
7. SSP/Ogg: keep 71 THz numeric coincidence distinct from unit-independent predictions.

## Scope and verification
No CI or Agda kernel check was run. New code is source-written; 'exact' in a filename denotes an intended proof form, not a verification receipt. Attribution: classical KK and Maxwell results belong to prior literature; PR #1239 donor is separately credited; this PR contributes the downstream observation-transport contract.
