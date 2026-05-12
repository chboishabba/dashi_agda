# Limited SM+GR Unification Claim Boundary

Status: non-promoting claim-governance document.

This document defines the publishable claim levels for DASHI on the path from
formal collider contact to limited known-limit SM/QFT + GR recovery. It does not
add a theorem, authority token, physical calibration receipt, stress-energy
receipt, Einstein-law receipt, or GRQFT promotion receipt.

## Control Frame

O: Noether owns this claim-boundary lane. The relevant consumers are W3, W4/W5,
Candidate256 physical calibration, W4 matter/stress-energy, discrete Einstein
law, and GRQFT/QFT validation.

R: Publication language must be gated by inhabited receipts. Request surfaces,
diagnostics, local probes, and preflight contracts cannot be described as closed
physics recovery.

C: This document is the governing artifact. It cites local receipt surfaces but
does not alter them.

S: Current local surfaces expose a staged route, not a completed unification
claim. W3 has a provider-response skeleton but no accepted authority token.
W4/W5 have accepted-DY-convention request/response infrastructure but no
accepted convention authority. W4 calibration, matter/stress-energy, discrete
Einstein law, and GRQFT validation remain downstream gates.

L: Claim levels are ordered by promotion strength:

1. Level 1: W3 empirical formal/collider paper.
2. Level 2: W3 + W4/W5 cross-band Drell-Yan paper.
3. Level 3: limited SM/QFT + GR known-limit recovery paper.

P: Publish only at the highest level whose required receipts are inhabited.

G: No promotion by prose. Constructorless tokens, external authority receipts,
and downstream theorem consumers must be inhabited before their claim level is
used.

F: The present gaps are accepted W3 authority, accepted DY luminosity convention,
W4 adequacy, W5 correction, Candidate256 physical calibration, W4 matter and
stress-energy, discrete Einstein law, GR/QFT laws, and empirical GRQFT
validation.

## Local Evidence Surfaces

- W3 provider-response gate:
  `DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenReceipt.agda`
- Accepted DY authority gate:
  `DASHI/Physics/Closure/AcceptedDYLuminosityConventionAuthorityReceipt.agda`
- W4/W5 shared DY/PDF dependency:
  `DASHI/Physics/Closure/W4W5AcceptedDYLuminosityConventionDiagnostic.agda`
  and `DASHI/Physics/Closure/W4W5PDFSharedDependencyDiagnostic.agda`
- W4 Z-peak adequacy gate:
  `DASHI/Physics/Closure/W4ZAdequacyReceipt.agda`
- W5 t45 correction gate:
  `DASHI/Physics/Closure/W5T45CorrectionReceipt.agda`
- W4 physical calibration queue:
  `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda`
  and `DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda`
- W4 matter/stress-energy preflight:
  `DASHI/Physics/Closure/W4MatterStressEnergyInterfaceReceipt.agda`
- Discrete Einstein-law candidate:
  `DASHI/Physics/Closure/EinsteinEquationCandidate.agda`
- GRQFT/QFT validation and promotion boundary:
  `DASHI/Physics/Closure/GRQFTConsumerSourceDiagnostic.agda`,
  `DASHI/Physics/Closure/GRQFTConsumerNextObligation.agda`, and
  `DASHI/Physics/Closure/GRQFTClosurePromotionReceiptRequestPack.agda`

## Level 1: W3 Empirical Formal/Collider Paper

### Admissible Claim

DASHI has a formal, reproducible W3 Drell-Yan empirical-contact result whose
accepted-evidence authority is externally reviewable and whose scope is limited
to the named W3 observable and comparison law.

This level can support a formal-methods/collider-phenomenology paper about a
machine-checkable empirical receipt chain for one collider observable. It is not
a cross-band result and not a SM+GR recovery claim.

### Required Receipts

- W3 comparison-law receipt and non-collapse witness already referenced by the
  W3 authority intake surfaces.
- `W3AcceptedEvidenceAuthorityTokenReceipt`, including:
  - an accepted provider response,
  - an inhabited `W3AcceptedEvidenceAuthorityToken`,
  - provider identity,
  - binding to HEPData/CMS sources,
  - binding to the frozen commit and covariance/source convention.

### Theorem Consumers

- W3 empirical receipt consumers only.
- W7/paper-governance consumers may cite W3 as an accepted empirical anchor only
  after the W3 authority token is inhabited.

### Empirical And Authority Gates

- External or accepted authority must certify the W3 evidence packet.
- Public-source fields alone are not enough unless repo governance explicitly
  accepts self-issuance for public-source evidence tokens.

### Forbidden Claims

- Do not claim W4 Z-peak adequacy.
- Do not claim W5 t45 correction or PDF closure.
- Do not claim physical calibration, matter, stress-energy, GR recovery, QFT
  interaction law, GRQFT validation, or physics unification.
- Do not describe W3 authority request/response skeletons as an accepted token.

### Stop Conditions

Stop at Level 1 if any of the following remains true:

- `W3AcceptedEvidenceAuthorityToken` is missing.
- The provider response is rejected or insufficient.
- The authority response does not bind the exact comparison law, source data,
  covariance, frozen commit, and non-collapse witness.

## Level 2: W3 + W4/W5 Cross-Band Drell-Yan Paper

### Admissible Claim

DASHI has an accepted W3 empirical anchor and a provider-governed cross-band
Drell-Yan comparison over W3 plus W4/W5, using an accepted parton-luminosity and
bin-integration convention.

This level can support a cross-band collider/phenomenology paper. It does not
yet support physical calibration or GR recovery.

### Required Receipts

- All Level 1 receipts.
- `AcceptedDYLuminosityConventionAuthority`, including:
  - PDF set/version and member,
  - LHAPDF or equivalent grid identifier,
  - grid checksum/provenance,
  - factorization and renormalization scale convention,
  - rapidity-window and mass-bin integration rules,
  - flavour and electroweak charge weights,
  - interpolation/integration method,
  - no-manual-overfit attestation,
  - authority statement that the convention is acceptable for W4/W5 comparison.
- `W4ZAdequacyReceipt` under that accepted convention.
- `W5T45CorrectionReceipt` under that accepted convention, or an explicit typed
  negative receipt if the accepted convention fails the target.

### Theorem Consumers

- W3 accepted empirical consumers.
- W4 Z-peak adequacy consumer.
- W5 t45 correction consumer.
- Cross-band Drell-Yan governance consumers.

### Empirical And Authority Gates

- Accepted DY convention authority is the shared W4/W5 choke point.
- W4 adequacy must be recomputed under the accepted convention, not under local
  exploratory CT18 probes.
- W5 t45 correction must be computed from the same accepted convention and
  reported with provenance and tolerance.

### Forbidden Claims

- Do not claim Candidate256 physical calibration.
- Do not claim matter field or stress-energy construction.
- Do not claim sourced non-flat GR geometry.
- Do not claim `G_mu_nu = 8 pi T_mu_nu`.
- Do not claim QFT interaction-law closure or GRQFT promotion.
- Do not call a failed W5 accepted-convention run a closure. A clean negative
  result is an obstruction, not a promotion.

### Stop Conditions

Stop at Level 2 if any of the following remains true:

- Accepted DY luminosity convention authority is missing.
- W4 Z-peak adequacy is missing, rejected, or fails its threshold.
- W5 t45 correction receipt is missing or fails without an accepted negative
  obstruction framing.
- The W4 and W5 calculations use different conventions, data provenance, or
  tolerances.

## Level 3: Limited SM/QFT + GR Known-Limit Recovery Paper

### Admissible Claim

DASHI supplies a limited known-limit recovery chain in which accepted
Drell-Yan evidence and accepted W4/W5 convention support physical calibration,
which then supports a W4-derived matter field, a W4-derived stress-energy
tensor, a discrete Einstein-law receipt, and limited GRQFT/QFT consumer
validation in the named regime.

This is the narrowest defensible SM/QFT + GR unification paper target. It is not
a full physics-unification claim.

### Required Receipts

- All Level 1 and Level 2 receipts.
- `Candidate256PhysicalCalibrationExternalReceipt`, including:
  - physical unit carrier,
  - calibration map,
  - Candidate256 calibration constant,
  - quotient-scale factorization,
  - dimensional preservation law,
  - external authority citation,
  - validation payload.
- `W4MatterStressEnergyInterfaceReceipt`, including:
  - `matterFieldFromW4`,
  - `stressEnergyTensorFromW4`,
  - explicit consumption of the Candidate256 physical calibration receipt.
- Discrete Einstein-law receipt, including:
  - W4 stress-energy source,
  - geometric carrier,
  - known-limit regime,
  - `grEquationLaw`,
  - `grEquationLawAtConsumer`.
- GRQFT/QFT closure evidence, including:
  - promotion authority,
  - external PDF carrier prerequisite if still required,
  - `qftInteractionLaw`,
  - `qftInteractionLawAtConsumer`,
  - downstream consumer fields,
  - empirical GRQFT validation receipt,
  - `GRQFTClosurePromotionReceipt`.

### Theorem Consumers

- W3 accepted empirical consumer.
- W4/W5 cross-band Drell-Yan consumers.
- Candidate256 physical-calibration consumer.
- W4 matter/stress-energy consumer.
- Discrete Einstein-law consumer.
- Limited GRQFT/QFT consumer in the same known-limit regime.

### Empirical And Authority Gates

- Candidate256 physical calibration must be externally or governance-accepted;
  the quotient/cross-band witness alone is not physical calibration.
- Matter and stress-energy must be derived from the accepted W4 physical
  calibration receipt.
- Einstein-law recovery must consume the W4 stress-energy tensor, not a
  placeholder source.
- GRQFT/QFT validation must be empirical and tied to the same downstream laws
  being promoted.

### Forbidden Claims

- Do not claim full Standard Model coverage.
- Do not claim full GR recovery outside the named known-limit regime.
- Do not claim quantum gravity or complete unification.
- Do not claim gravity recovery from flat-space/Minkowski surfaces alone.
- Do not claim matter coupling from W4 request surfaces alone.
- Do not claim GRQFT closure from known-limits bridge availability alone.
- Do not claim that authority/provider packets are receipts.

### Stop Conditions

Stop at Level 3 if any of the following remains true:

- Candidate256 physical calibration receipt is missing.
- `matterFieldFromW4` or `stressEnergyTensorFromW4` is missing.
- Discrete Einstein-law receipt is missing or only a candidate surface exists.
- GR equation law, QFT interaction law, or consumer witness is missing.
- Empirical GRQFT validation receipt is missing.
- The proposed paper language would require broad SM coverage, full GR recovery,
  quantum gravity, or full unification.

## Global Forbidden Claims

The following claims are forbidden at all levels until separately promoted by
inhabited receipts:

- "DASHI unifies physics."
- "DASHI has recovered the full Standard Model."
- "DASHI has recovered full general relativity."
- "DASHI has quantum gravity closure."
- "DASHI has full SM+GR unification."
- "W4/W5 are closed because CT18 is local."
- "A provider packet is an authority receipt."
- "A local diagnostic or negative audit is a promotion."
- "A flat-space GR surface is a sourced Einstein-law recovery."
- "Candidate256 quotient evidence is physical calibration authority."

## Publication Decision Rule

Before submission, choose the highest level whose required receipts are actually
inhabited.

- If only W3 authority is accepted, submit a Level 1 paper.
- If W3 authority plus accepted W4/W5 Drell-Yan convention, W4 adequacy, and W5
  correction are accepted, submit a Level 2 paper.
- If Candidate256 calibration, W4 matter/stress-energy, discrete Einstein law,
  and GRQFT/QFT validation are accepted in addition to Level 2, submit a Level 3
  limited known-limit SM/QFT + GR paper.

If any authority, empirical, or theorem consumer is request-only, use the lower
claim level. If the lower claim level still relies on that request-only surface,
do not submit yet.
