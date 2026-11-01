# TSFV Candidate256 Calibration Roadmap

Date: `2026-05-12`
Status: `roadmap plus typed diagnostic; non-promoting`
Owner: `Lagrange / TSFV calibration-law theorem lane`

## Scope

This note scopes the missing TSFV-compatible calibration law for the
Drosophila/Candidate256 W4 support path.

Inputs already present locally:

- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda`
- `Docs/DrosophilaGenomeW4CandidateAuthority.md`
- `scripts/data/genome/drosophila_release6_authority_packet.json`
- `DASHI/Physics/Closure/W4SurrogateScaleSettingBoundary.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda`

The genome packet is a checksum-bound candidate input only. It records Release
6 authority metadata, FASTA checksums, and a CDS codon non-uniformity witness.
It does not construct a TSFV calibration law, Candidate256 authority token,
Candidate256 physical-calibration receipt, W4 promotion, or unification claim.

## Local Typed Diagnostic

`DASHI/Physics/Closure/TSFVCandidate256CalibrationLawDiagnostic.agda` defines
the missing law shape:

```text
TSFVCompatibleCandidate256CalibrationLaw
```

The shape requires:

- a TSFV physical unit carrier
- a `Nat -> TSFV-unit` calibration map
- a Candidate256 quotient-class scale map over the existing quotient carrier
- factorization through `candidate256SurrogateScale`
- an `L_chem` dimensional-preservation law and inhabitant at the Candidate256
  quotient-law witness
- nontrivial calibrated separation of the Candidate256 left and right quotient
  classes

The diagnostic intentionally sets these to `false`:

- `constructsTSFVCalibrationLaw`
- `constructsCandidate256PhysicalCalibrationAuthorityToken`
- `constructsCandidate256PhysicalCalibrationExternalReceipt`
- `promotesW4`
- `promotesPhysicsLane`
- `claimsUnification`

## Roadmap

1. Treat the Drosophila Release 6 CDS/codon packet as candidate input only.
2. Specify the TSFV physical unit carrier and why it is physically meaningful.
3. Provide a `Nat -> TSFV-unit` calibration map for the Candidate256 surrogate
   scale values.
4. Provide a quotient-class map
   `Candidate256QuotientClass -> TSFV-unit`.
5. Prove the quotient-class map factors through the existing
   `candidate256SurrogateScale`.
6. State and inhabit the `L_chem` dimensional-preservation law at the
   Candidate256 quotient-law witness.
7. Prove the calibrated left and right quotient classes remain nontrivially
   separated.
8. Submit the resulting law with a legitimate external
   `Candidate256PhysicalCalibrationAuthorityToken` artifact.
9. Only after that, package a
   `Candidate256PhysicalCalibrationExternalReceipt`.

## Exact Remaining Theorem Obligations

1. `TSFV physical unit carrier`
   - A carrier with physical interpretation, not the current dimensionless
     `Nat` surrogate.

2. `Nat-to-TSFV-unit calibration map`
   - A map from `candidate256SurrogateScale` values into the TSFV unit carrier.

3. `Candidate256 quotient-class scale map`
   - A map from the existing Candidate256 quotient carrier into TSFV units.

4. `Factorization through Candidate256 surrogate`
   - For every Candidate256 quotient class `q`, prove the TSFV quotient map
     equals the TSFV calibration of `candidate256SurrogateScale q`.

5. `L_chem dimensional preservation`
   - A law family over `canonicalCandidate256QuotientLaw` and an inhabitant at
     each quotient-law witness.

6. `Nontrivial calibrated left/right separation`
   - Prove the calibrated left and right Candidate256 quotient classes do not
     collapse after TSFV calibration.

7. `Candidate256 physical-calibration authority`
   - Supply a legitimate external artifact for the constructorless
     `Candidate256PhysicalCalibrationAuthorityToken`.

8. `Candidate256 physical-calibration receipt`
   - Package the authority token, unit carrier, calibration maps,
     factorization law, dimensional-preservation law, and labels into
     `Candidate256PhysicalCalibrationExternalReceipt`.

## Non-Claim Boundary

This tranche does not fabricate tokens, promote W4, promote physics, claim
biological recovery, or claim unification. The Drosophila genome packet remains
candidate evidence for a provider-facing calibration-law request.
