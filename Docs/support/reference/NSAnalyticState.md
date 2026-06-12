# Navier-Stokes Analytic State

Status: Paper 1 is now an honest reduction manuscript; the live Clay frontier
is the coupled `A1/A3` bootstrap plus the quantitative `A4`
Lei-Ren-Tian-to-Fourier transfer.

## What Landed

1. Reduction-manuscript reset
   - Surface: `Docs/papers/live/Paper1NavierStokesClayDraft.md`
   - Result: Paper 1 is now explicitly a conditional blowup-reduction paper
     organized around `A1-A9`, with the constants ladder promoted to
     theorem-sized propositions and the main analytic burden localized.
   - Boundary: this is not a Clay proof and does not pretend that `A1-A9` are
     already discharged.

2. A1/A3 split frontier
   - Receipts: `NSAbelTriadicStationarityConstructionBoundary`,
     `NSBoundedAbelMassEstimateBoundary`,
     `NSQuantitativeStationarityRateBoundary`
   - Result: the repo now names the live coupled wall honestly: construct the
     Abel-weighted triadic defect measure with quantitative compactness and
     prove enough approximate `T_NS`-stationarity to close the bootstrap.
  - Boundary: the repo now carries an exact candidate theorem package for
    `A1.1-A3.4`, including explicit candidate constants and rates, but the
    closure remains fail-closed until those calculations are accepted in the
    exact normed setting consumed downstream by `A6-A8`. In particular, the
    current candidate `epsilon = 1/6` Seregin/ESS intake and
    `delta_r = O(r^(1/12))` stationarity rate are recorded as concrete theorem
    targets rather than promoted local theorems.
   - Exact live lemma ladder:
     `A1.1` bounded Abel-weighted defect mass,
     `A1.2` weak-* tightness / precompactness,
     `A1.3` quantitative shell-tail control,
     `A3.1` energy ODE for `W_r = U_r - U_infinity`,
     `A3.2` imported Seregin/ESS epsilon-rate intake,
     `A3.3` `delta_r -> 0` quantitative stationarity,
     `A3.4` multiscale Abel-summation closure with no hidden exponent loss.
  - Verification posture: the candidate theorem package is now:
    bounded Abel-weighted defect mass with explicit constant,
    weak-* tightness with explicit tail radius,
    quantitative shell-tail control,
    localized energy ODE for `W_r`,
    imported ESS/Seregin rate with `epsilon = 1/6`,
    stationarity-defect rate `delta_r = O(r^(1/12))`,
    and multiscale Abel-summation closure with finite geometric constants.
    These are recorded as the exact inputs Paper 1 would consume if promoted;
    they are not yet treated as locally discharged theorems.

3. A4 transfer ladder
   - Receipts: `NSLeiRenTianOutputSupportTransferBoundary`,
     `NSWhitneyCouplingInequalityBoundary`,
     `NSPhiJacobianLowerBoundBoundary`, and the A4 child/composite surfaces
   - Result: the physical-angular-richness -> Fourier-output-richness theorem
     is now decomposed into its Jacobian/coarea/Whitney obligations.
  - Boundary: the repo now carries an exact candidate A4 theorem package:
    direction-map regularity, Jacobian lower bound, coarea propagation,
    strip-hitting richness, and a rescaling-uniform lower bound. The
    governance posture remains fail-closed until that package is accepted as a
    usable theorem in the precise output-support form consumed by `A5-A6`.
   - Exact live lemma ladder:
     `A4.1` direction-map regularity,
     `A4.2` Jacobian lower-bound / nondegeneracy route,
     `A4.3` coarea propagation,
     `A4.4` strip-hitting / pushforward richness,
     `A4.5` uniformity across the Type-I rescaling family.

4. Downstream route organization
   - Receipts: `NSA5KappaBiasVanishingFromA4StationarityBoundary`,
     `NSPointwiseToAbelCompositeA6Boundary`,
     `NSA7ResidualDepletionGronwallBoundary`,
     `NSA8A9MonotonicityClosureTheoremLadderBoundary`
   - Result: once `A1/A3` and `A4` are available, the later A5-A9 stages are
     organized as downstream consumers rather than free-floating blockers.
   - Boundary: these stages are not yet promoted independently of the earlier
     fronts, but the repo now records an exact candidate downstream theorem
     package rather than generic placeholders.
   - Exact candidate downstream package:
     `A5` kappa-bias vanishing from asymptotic stationarity plus A4 richness,
     `A6` pointwise-to-Abel / leakage inequality with explicit transport,
     commutator, and stretching budgets,
     `A7` Gronwall depletion threshold,
     `A8` scale-monotonicity recursion,
     `A9` CKN/BKM contradiction.
   - Verification posture: this package is recorded so the referee-facing
   route is exact once `A1/A3` and `A4` are accepted. It does not upgrade
   the current governance state; every theorem and Clay flag remains
   fail-closed until the upstream fronts are promoted.

5. Classical-theorem intake is now sharply packetized
   - Receipts: the CKN / ESS / LRT packet surfaces, the standard PDE writeup
     assembly surface, and the reviewer-facing NS packet surfaces.
   - Result: the repo now treats the classical PDE intake as exact theorem
     grammar rather than generic external fog. CKN local-energy and
     epsilon-regularity, ESS backward-uniqueness / Carleman, and the
     Lei-Ren-Tian angular-richness ladder are each named as concrete theorem
     packets feeding `A1/A3`, `A4`, and the downstream `A5-A9` route.
   - Boundary: this sharpens the self-contained packet story only. It does not
     by itself promote the NS candidate package to a proved Clay theorem.

## Diagnostic

The older theta/danger-shell diagnostics are still useful as obstruction
guidance, but they are no longer the main manuscript grammar. Their honest role
is to explain why the near-diagonal high-high interaction is the right seam to
localize before one asks for Abel-defect compactness, quantitative
stationarity, and the later support-geometry transfer. They remain diagnostic
evidence only.

## Remaining NS Burden

The remaining NS burden is now governance-shaped rather than theorem-shape
shaped.

1. Accept or reject the candidate self-contained `A1.1-A3.4` package in the
   exact norms consumed by the downstream Abel/leakage route.
2. Accept or reject the candidate self-contained `A4.1-A4.5` package with a
   uniform Type-I-rescaling constant in the exact output-support form used by
   `A5-A6`.
3. If those two packages are accepted, the already recorded `A5-A9` ladder is
   available as the downstream consumer path into kappa-bias vanishing,
   pointwise-to-Abel averaging, depletion, monotonicity, and the final
   CKN/BKM contradiction.

In other words, the repo no longer lacks theorem grammar for the NS Clay lane.
It now carries an explicit candidate self-contained packet
`CKN + ESS + LRT + A1/A3 + A4 + A5-A9`. What remains fail-closed is the
promotion decision: whether those candidate calculations and constants are
accepted as the exact theorem inputs consumed by Paper 1.

## Publication Posture

Publishable claim: Paper 1 is an honest reduction manuscript with a sharp
frontier. The repo now carries an explicit classical PDE packet
`CKN + ESS + LRT + A1/A3 + A4 + A5-A9` in reviewer-readable form, while the
live new mathematics remains concentrated in the coupled `A1/A3` bootstrap and
the `A4` uniform output-support transfer.

Forbidden claim: unconditional regularity or Clay promotion.
