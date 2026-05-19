# Atom And Wave Recovery Status

Declared surface level: `packaging`.

This note is the canonical public status surface for the repo's atom-adjacent
and wave-adjacent material.

It exists to stop one specific underclaim:

- the repo already has real shell/orbit/profile and wave-regime formalism
- the archive already has stronger atom/chemistry dictionary language
- neither of those facts, by themselves, is a finished atomic-physics or
  chemistry recovery theorem

## Current Read

The strongest honest current claim is:

- local Agda already contains substantial theorem-bearing shell/orbit/profile
  structure and a theorem-bearing known-limits recovered-wave ladder
- the archive already supports atom/chemistry correspondence language around
  typed dictionaries, Pauli-style exclusion, MDL-style shell filling, and
  closed-shell behavior
- the remaining gap is not "do atoms or waves appear at all?"
- the remaining gap is promotion to a physically interpreted recovery theorem
  with scale, spectra, and stronger quantum/chemistry observables

## 1. Formalized / Theorem-Bearing Now

### Shell / Orbit / Profile

- `DASHI.Physics.OrbitProfileComputed`
  and `DASHI.Physics.OrbitProfileComputedSignedPermEvidence` compute and expose
  the orbit-profile object used as the shell/signature keystone.
- `DASHI.Physics.Signature31FromShiftOrbitProfile`
  and `DASHI.Geometry.Signature31FromIntrinsicShellForcing` are part of the
  theorem-bearing route into the local `(3,1)` signature target.
- `DASHI.Physics.ConeArrowIsotropyOrbitProfileAgreement`
  and `DASHI.Physics.ConeArrowIsotropyForcesProfileShiftInstance` package the
  current measured/forced profile agreement on the shift-side witness.
- `DASHI.Physics.Closure.SyntheticRealizationWitness`
  packages shell-neighborhood preservation, shell-1 and shell-2 profile
  preservation, promotion readiness, dynamics readiness, and canonical
  signature matching on the synthetic one-minus realization.

### Wave / Regime

- `DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem`
  gives the canonical wave-lift bridge on the closure path.
- `DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem`,
  `KnownLimitsRecoveredWaveGeometryTheorem`,
  `KnownLimitsRecoveredWaveRegimeTheorem`, and
  `KnownLimitsRecoveredWaveObservablesTheorem`
  form a real theorem-bearing known-limits wave ladder.
- `DASHI.Physics.Closure.CanonicalWaveObservableConsumer`,
  `CanonicalWaveGeometryConsumer`, and `CanonicalWaveRegimeConsumer`
  show that the wave ladder is actually consumed on the canonical side.

## 2. Bounded Scaffold / Interface

- `DASHI.Physics.DashiDynamics` provides a shared state / observable /
  density-action-amplitude interface.
- `DASHI.Physics.PressureHamiltonJacobiGap`,
  `PressureGradientFlowGap`, and `SchrodingerGap`
  are honest theorem-thin consumers with explicit non-claim boundaries.
- `DASHI.Physics.SchrodingerGapShiftInstance`
  gives a bounded pressure-ordered inhabitant with density and amplitude
  proxies, while explicitly refusing a physical Schrödinger derivation.
- `DASHI.Physics.ShiftPhaseWaveContinuumStory`,
  `ShiftPhaseTableInterference`, `ShiftDiscreteWaveStep`,
  `ShiftWaveScalingInterface`, and `ShiftWaveRefinementSeam`
  show that the finite phase / interference / refinement lane is active and
  formalized, not just prose.
- `DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic` records the
  current W4 chemistry state after carrier-policy acceptance: the accepted
  retargeted schedule-MDL carrier and Candidate256 quotient/cross-band law form
  a pre-handoff receipt, but the status remains
  `retargetedQuotientPrePhysicalConsumerAvailable`. The consumer is deliberately
  boundary-only: its carrier is the landed quotient carrier and its meaning is
  only the pre-spectral/pre-scale-setting boundary pair.
- `DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker` records the
  next W4 physical-semantics gap without promoting it: strict physical semantics
  require separate scale-setting, spectral observable, bonding interpretation,
  and empirical physical validation carriers/laws beyond the pre-physical
  quotient boundary.
- `DASHI.Physics.Closure.W4StrictPhysicalNextObligation` packages those strict
  physical-semantics fields as an obligation surface tied to the accepted
  retargeted carrier and Candidate256 quotient law. It is deliberately not an
  inhabited physical-chemistry theorem.
- `DASHI.Physics.Closure.W4StrictPhysicalObligationLedger` orders those
  obligations for downstream work: scale-setting first, then spectral
  observable, bonding interpretation, and empirical physical validation. Each
  lane remains marked `obligationNeededUninhabitedHere`.
- `DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation` narrows the
  first strict physical lane to a physical scale carrier, quotient-class scale
  map, and `L_chem` scale-preservation law requirement. It does not inhabit a
  scale-setting law or strict physical consumer.
- `DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary` shows the scale lane
  can be inhabited as a dimensionless `Nat` diagonal `I× (q , q)` over
  Candidate256 quotient classes. It is explicitly not a physical unit system,
  calibration, spectrum, bonding interpretation, or empirical validation.
- `DASHI.Physics.Closure.W4PhysicalCalibrationGate` records the promotion gate
  from that surrogate to physical scale-setting: a physical unit carrier,
  Nat-to-unit calibration map, calibrated quotient scale map, and dimensional
  preservation law are required before the scale lane can promote. Its
  physical calibration authority token has no constructors in the current repo,
  so the dimensionless `Nat` surrogate cannot be reused as calibrated physical
  units without a new upstream authority receipt.
- `DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation` names
  that upstream receipt shape explicitly: it must carry calibration authority,
  physical units, Nat-to-unit calibration, calibrated quotient scale
  factorization, and dimensional preservation. The current status remains
  obligations-needed/blocked.

## 3. Archive-Supported Interpretation

Archive anchors:

- `DASHI Atom` — `25ec0d2e654f33ea6f524f816b4c465e86ef21cf`
- `Physics Closure in DASHI` — `2fa5dc5c445be6ce34c31cf6d2d9f94c6d029320`
- `Branch · Math Mysticism Breakdown` —
  `54e662a4243d10d575758d394f3c472210ed7cd2`
- `Dashi and Physics Insights` —
  `ad17536d8eeb320106585654a0950424abafa93b`

What the archive supports safely:

- atoms and molecules as typed dictionary / quotient-level correspondence
  language
- Pauli-style exclusion as part of the shell-filling story
- MDL-style shell-filling intuition
- closed-shell or saturated-kernel language for inert states
- chemistry as quotient-observable behavior rather than raw microstate detail

What the archive does not yet justify as repo-native theorem closure:

- full atomic spectra recovery
- full bonding or chemistry recovery
- full DFT/QED/QFT derivation from the canonical closure stack
- strong periodic-table or ionization-energy theorem claims

## 4. Still Open

- a canonical theorem for shell occupancy / filling that is defended at the
  same level as the formal closure spine
- a physical scale-setting layer that turns structure-before-scale into
  spectra, ionization, or chemistry numerics
- a non-proxy wave / Schrödinger / Hamiltonian derivation from the closure core
- a continuum/scaling-limit theorem that reaches a nontrivial quantum carrier
- a theorem that links the current shell/profile invariants to atom-facing
  observables on a physically interpretable carrier
- a typed physical interpretation carrier, quotient-class interpreter,
  retargeted-carrier preservation law, quotient-law preservation law, and
  boundary preservation for the quotient classes over the accepted retargeted
  carrier
- stronger physical semantics beyond the boundary-only pre-physical consumer:
  scale setting, spectra, bonding, wet-lab chemistry, or physical validation
  with preservation laws over the Candidate256 quotient witness

## Formal Owner Modules

- `DASHI.Physics.OrbitProfileComputed`
- `DASHI.Physics.OrbitProfileComputedSignedPermEvidence`
- `DASHI.Physics.Signature31FromShiftOrbitProfile`
- `DASHI.Physics.ConeArrowIsotropyOrbitProfileAgreement`
- `DASHI.Physics.ConeArrowIsotropyForcesProfileShiftInstance`
- `DASHI.Physics.Closure.SyntheticRealizationWitness`
- `DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem`
- `DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem`
- `DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem`
- `DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem`
- `DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem`
- `DASHI.Physics.DashiDynamics`
- `DASHI.Physics.SchrodingerGap`
- `DASHI.Physics.ShiftPhaseWaveContinuumStory`
- `DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic`
- `DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker`
- `DASHI.Physics.Closure.W4StrictPhysicalNextObligation`
- `DASHI.Physics.Closure.W4StrictPhysicalObligationLedger`
- `DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation`
- `DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary`
- `DASHI.Physics.Closure.W4PhysicalCalibrationGate`
- `DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation`

## Not This / Out Of Scope

- a claim that the repo has already derived chemistry or atomic spectra
- a claim that the finite wave lane already yields textbook quantum mechanics
- a claim that archive-only atom language is automatically repo-native proof
- a replacement for `Docs/PhysicsRecoveryLedger.md` or
  `Docs/ArchiveRecoveryCrosswalk.md`
