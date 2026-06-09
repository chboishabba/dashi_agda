# Paper 6 Status After Phase 1

Status date: 2026-05-30

> **Superseded 2026-05-31.** This file records the Phase 1 diagnostic state,
> not the current prewrite baseline.  The current Paper 6 outline is
> `Paper6FinalDraftOutline.md`: `|Vcb|`, `A`, direct CP angle readbacks, and
> full CKM quantities are not promoted carrier predictions.

Paper 6 should be presented as a diagnostic/conjecture paper.  Phase 1 does
not deliver a physical CKM derivation, a physical quark/lepton derivation, or a
Standard Model reconstruction.  It delivers a sharpened map of which Heegner
lane numerics are clean, which are candidate-only, and which routes have been
tested negatively.

## Clean Diagnostic Results

- Lambda is the cleanest CKM diagnostic.  The carrier formula records
  `lambda ~= 0.224403`, with the submission-facing comparison summarized as
  about `0.04%` from the chosen PDG-sized target.  Cite
  `DASHI.Physics.Closure.WolfensteinLambdaAFromCarrierReceipt` and
  `DASHI.Physics.Closure.WolfensteinFullDiagnosticReceipt`.
- The A/Vcb lane is sharp only after geometric resummation.  The Phase 1
  status is `A ~= 0.8255982974`, about `0.05%` from the PDG-sized A target.
  This is still diagnostic: the origin of the geometric resummation is not
  proved.  Cite `DASHI.Physics.Closure.VcbGeometricResummationReceipt`.

## Candidate Routes

- Vub has a candidate degree-28 route.  The degree-28 compositum diagnostic
  gives `|Vub| ~= 0.0034300644` before the NLO factor and
  `|Vub| ~= 0.0036780010` with the NLO QCD factor.  The NLO factor improves the
  comparison but is explicitly not carrier-derived, so this is not a physical
  Vub derivation.  Cite `DASHI.Physics.Closure.Vub28IsogenyReceipt`.
- The CP phase remains open.  The p=29 Hecke-character phase is concrete, but
  it does not match the PDG-sized phase target and does not derive physical CP.
  Cite `DASHI.Physics.Closure.HeckeCharacterPhaseReceipt` and
  `DASHI.Physics.Closure.Y13ComplexEntryReceipt`.
- Structural charge quantisation is a useful finite-lane result, not a full
  gauge-sector derivation.  The p3-lane `Z/6` surface records sixth-unit charge
  bookkeeping while continuous `U(1)_Y`, exact normalization, anomaly
  cancellation, and full SM promotion remain false.  Cite
  `DASHI.Physics.QFT.SMChargeQuantisationReceipt`,
  `DASHI.Physics.QFT.U1YFromConductorReceipt`, and
  `DASHI.Physics.QFT.ChargeNormalisationReceipt`.
- The Heegner-position quark/lepton hypothesis is sharpened but open.  The
  p2 quark lane `D=-4, j=1728, Z[i], Z4, conductor 4` and the D=-8 lepton lane
  `D=-8, j=8000, Z[sqrt(-2)], Z2, conductor 8` are recorded as a separation
  candidate.  The unit-group ratio `4/2=2` does not yield SM charge ratios, and
  the separation mechanism is not identified.  Cite
  `DASHI.Physics.Closure.LeptonQuarkSeparationReceipt` and
  `DASHI.Physics.QFT.QuarkLeptonCMUnitGroupReceipt`.

## Closed Negative Routes

Phase 1 also closed several tempting explanations as negative diagnostics:

- Faltings height: the direct Faltings-height route for the deg23 residual was
  tested and does not resolve the residual.  Cite
  `DASHI.Physics.Closure.FaltingsHeightDeg23Receipt` and
  `DASHI.Physics.Closure.Deg23FaltingsComputationReceipt`.
- RG-running: the deg23 RG-running hypothesis was recorded and remains
  non-promoting; it is not a closed carrier derivation of the required
  correction.  Cite `DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt` and
  `DASHI.Physics.Closure.Deg23RGRunningHypothesisReceipt`.
- Hecke eigenvalue recipes: the Hecke-eigenvalue route does not cleanly derive
  the required lane-dimension or charge table.  Cite
  `DASHI.Physics.Closure.PrimeLaneGaugeAssignmentReceiptSurface`.
- Phi/golden-ratio routes: phi appears in useful diagnostics, but the
  golden-ratio pattern is not carrier-derived and does not promote Vub, CKM, or
  SM claims.  Cite `DASHI.Physics.Closure.GoldenRatioNumericsReceipt`,
  `DASHI.Physics.Closure.GoldenRatioUnifyingReceipt`, and
  `DASHI.Physics.Closure.RogersRamanujanP5Receipt`.
- Positional-gap explanations: Heegner position and conductor/discriminant
  bookkeeping help classify candidate lanes, but the positional gap by itself
  does not derive quark/lepton separation, charge ratios, or physical CKM
  structure.  Cite `DASHI.Physics.Closure.LeptonQuarkSeparationReceipt` and
  `DASHI.Physics.QFT.LeptonSectorGapReceipt`.

## Paper 6 Scope Statement

Paper 6 can honestly claim:

- a clean lambda diagnostic at about `0.04%`;
- a sharp A/Vcb diagnostic at about `0.05%` after geometric resummation, with
  the resummation origin unproved;
- a candidate degree-28 Vub route whose NLO improvement is not carrier-derived;
- an open CP phase route;
- structural finite charge quantisation and a Heegner-position quark/lepton
  hypothesis;
- a set of closed negative routes that prevent overclaiming.

Paper 6 must not claim:

- a physical CKM derivation;
- a physical Vub derivation;
- a physical CP-phase derivation;
- a quark/lepton separation theorem;
- a full Standard Model reconstruction.

The correct Phase 1 conclusion is that the Heegner lane assignment has strong
diagnostic evidence and useful conjectural structure, but the physical
mechanism remains open.
