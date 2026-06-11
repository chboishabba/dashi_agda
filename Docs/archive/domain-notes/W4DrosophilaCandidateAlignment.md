# W4 Drosophila Candidate Alignment

Owner: Nash, W4 kill-matrix alignment lane.

Status: non-promoting alignment artifact. This document aligns the new Drosophila Release 6 genome candidate packet against the actual W4 physical-calibration evidence fields. It does not close W4.

## ZKP Frame

O: W4 kill-matrix alignment lane. Candidate packet owner is local/documentary only; W4 authority remains external.

R: Distinguish candidate route, candidate evidence, accepted authority, and promotion. Align against the fields W4 actually requires: `acceptedAuthorityRoute`, `checksumBoundSelection`, `nontrivialWitness`, `calibrationLaw`, `physicalUnitCarrier`, and validation payload.

C: Local read sources:

- `Docs/DrosophilaGenomeW4CandidateAuthority.md`
- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationGate.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda`
- `DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationRouteNarrowing.agda`

S: The Drosophila packet is candidate-only, checksum-bound, and explicitly non-promoting. W4 remains blocked on accepted authority, W4 Z adequacy, external Candidate256 physical-calibration receipt, unit carrier, calibration/factorization/dimensional law, and validation payload.

L/P: Local read-and-document alignment. No Agda edits are needed for this pass because the candidate receipt already contains explicit boolean non-promotion fields.

G: No W4 close. Candidate evidence may reduce ambiguity for a future request, but it does not inhabit W4 authority tokens or promotion receipts.

F: Minimal path is to turn the candidate into a provider-facing request/diagnostic for accepted authority and calibration, not to treat the genome packet as W4 evidence by itself.

## Candidate Packet Summary

The candidate packet records:

- organism: `Drosophila melanogaster`
- assembly accession: `GCF_000001215.4`
- assembly name: `Release 6 plus ISO1 MT`
- Release 6 reference DOI: `10.1101/gr.185579.114`
- PubMed: `25589440`
- genomic FASTA SHA-256: `e69e907b5e87ce756236dcef93e82001cfd08f1a0ed5f22e36cbbd3a87ebc57d`
- CDS FASTA SHA-256: `3f379cec1d952f9a1c22e2b6dd9ff8eefce6da97ffb198cde93dc0a17c40da01`
- codon witness: 20,409,720 ACGT codons, 64 distinct codons, max `GAG`, min nonzero `TGA`, non-uniformity witness true

The Agda receipt names this status exactly as `candidateAuthorityAndChecksumBoundSelectionOnly`.

## Gap Table

| W4 evidence field | Actual W4 requirement | Drosophila candidate content | Alignment status | Gap |
|---|---|---|---|---|
| `acceptedAuthorityRoute` | W4 requires accepted external authority in the queue `AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt`. | `acceptedAuthorityRouteCandidate = true`; NCBI/Release 6 route is source-cited and checksum-bound. | Candidate-filled only. | Does not inhabit `AcceptedDYLuminosityConventionAuthority`, `Candidate256PhysicalCalibrationAuthorityToken`, or any W4 accepted authority route. |
| `checksumBoundSelection` | W4/provider fields require checksum-bound selection tied to the relevant calibration source and receipt chain. | Genome and CDS FASTA SHA-256 values plus generated packet path are recorded. | Candidate-filled for genome/CDS artifacts. | Not bound to W4 Z-peak calibration artifacts, DY luminosity convention, Candidate256 unit calibration, or W4 adequacy receipt. |
| `nontrivialWitness` | A useful candidate may provide a nontrivial observable, but W4 closure needs that witness to feed a calibration/physical law. | `codonNonuniformWitness = true`; codon distribution is non-uniform over the checksum-bound CDS FASTA. | Candidate-filled. | Non-uniform codon statistics are not a `calibrationLaw`, dimensional law, physical validation receipt, or Brain/W4 handoff proof. |
| `calibrationLaw` | W4 requires unit-bearing calibration: `calibrationAuthority`, `physicalUnitCarrier`, `natToUnitCalibrationMap`, `calibratedQuotientScaleMap`, factorization, and dimensional preservation. | Candidate receipt sets `constructsCalibrationLaw = false`. | Missing. | No W4SameRecord calibration law, no Candidate256 calibration law, no dimensional preservation theorem. |
| `physicalUnitCarrier` | `W4PhysicalCalibrationGate` and external receipt obligation require a physical unit carrier distinct from the dimensionless `Nat` surrogate. | Candidate receipt contains genome/CDS counts and checksums only. | Missing. | No `physicalUnitCarrier : Set`, no `unitCarrier`, no physical unit labels, no Nat-to-unit map. |
| `validationPayload` / validation payload | `Candidate256PhysicalCalibrationExternalReceipt` requires `validationPayload : List String`; W4 route also keeps physical validation downstream. | Candidate doc has local validation commands and a codon witness, but no W4 validation payload field. | Missing for W4. | Local script/Agda checks validate packet extraction/typechecking only; they are not physical calibration validation payload. |
| `sourceW4ZAdequacyReceipt` | Candidate256 external receipt requires `sourceW4ZAdequacyReceipt : W4ZAdequacyReceipt`. | Candidate packet has no W4 Z adequacy receipt. | Missing. | `W4ZAdequacyReceipt` remains downstream of accepted DY authority and impossible here. |
| `Candidate256PhysicalCalibrationAuthorityToken` | Constructorless W4 authority token is required before external calibration receipt can exist. | Candidate receipt sets `constructsCandidate256PhysicalCalibrationAuthorityToken = false`. | Missing. | Citation/checksum/prose cannot inhabit the constructorless token. |
| `Candidate256PhysicalCalibrationExternalReceipt` | Positive external receipt must carry accepted authority, W4 Z adequacy, authority token, unit carrier, scale maps, calibration constant, factorization, dimensional preservation, citation, and validation payload. | Candidate receipt sets `constructsCandidate256PhysicalCalibrationExternalReceipt = false`. | Missing. | All positive receipt constructors remain unavailable in-repo. |
| Brain/W4 handoff compatibility | Any use as chemistry support would need a proof into `BrainAtomicChemistryHandoffProfile` or strict W4 scale-setting fields. | Candidate receipt sets `constructsBrainAtomicChemistryHandoffProof = false`. | Missing. | No TSFV-compatible or BrainAtomicChemistryHandoff compatibility theorem exists. |
| Promotion | W4 promotion would require accepted authority and positive receipt chain. | Candidate receipt sets `promotesW4 = false`, `promotesPhysicsLane = false`, and `claimsUnification = false`. | Correctly blocked. | No W4 close. |

## Kill-Matrix Reading

The candidate can be credited for three things only:

- candidate authority route over a public Drosophila Release 6 source;
- checksum-bound selection of local genome/CDS artifacts;
- nontrivial, checksum-bound codon-frequency witness.

The candidate cannot kill the W4 blocker because it lacks the fields that the W4 gate and external receipt surfaces require:

- accepted DY authority or accepted W4 authority route;
- `W4ZAdequacyReceipt`;
- `Candidate256PhysicalCalibrationAuthorityToken`;
- `physicalUnitCarrier`;
- Nat-to-unit calibration map;
- quotient scale map and factorization through `candidate256SurrogateScale`;
- dimensional preservation law and witness;
- `validationPayload`;
- downstream spectra, bonding, and empirical physical-validation receipts.

## Candidate vs Evidence vs Authority vs Promotion

Candidate route: present. The packet identifies a plausible source route and rejects the prior DOI for this route.

Candidate evidence: present for checksums and codon non-uniformity.

Accepted authority: absent. The packet does not inhabit accepted DY authority, Candidate256 authority, or W4 external authority tokens.

Promotion: absent. The packet explicitly records no W4, Brain, physics, biological-recovery, or unification promotion.

## Minimal Next Closure Path

1. Preserve this packet as a candidate authority/checksum/nontrivial-witness input only.
2. If W4 wants to consume it, add a provider-facing diagnostic/request that maps the codon witness into a proposed chemistry-law compatibility target, not a promotion.
3. Obtain or define the missing accepted authority route that W4 actually asks for: currently the queue starts with `AcceptedDYLuminosityConventionAuthority`, then `W4ZAdequacy`.
4. Only after that, pursue `Candidate256PhysicalCalibrationExternalReceipt` with `unitCarrier`, `scaleMap`, `quotientScaleMap`, `candidate256CalibrationConstant`, factorization, dimensional preservation, external authority citation, and `validationPayload`.
5. Keep strict physical downstream lanes separate: spectra, bonding, and empirical physical validation remain after scale-setting.

## Grep Evidence

- `Docs/DrosophilaGenomeW4CandidateAuthority.md:76-83`: board interpretation marks accepted authority route, checksum selection, and nontrivial witness as candidate-only, while calibration law and external receipt are missing.
- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda:13-17`: candidate receipt says it is not a W4 physical-calibration receipt and the authority token remains uninhabited.
- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda:95-104`: candidate booleans for accepted authority route, checksum selection, and non-promotion-critical missing fields.
- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda:189-217`: candidate fields are true for route/checksum/witness and false for calibration, Candidate256 authority, external receipt, handoff proof, W4 promotion, and unification.
- `DASHI/Physics/Closure/W4PhysicalCalibrationGate.agda:26-47`: W4 physical calibration requires a constructorless authority token, physical unit carrier, calibration map, quotient scale map, factorization, and dimensional-preservation law.
- `DASHI/Physics/Closure/W4PhysicalCalibrationGate.agda:155-169`: current W4 status says no physical unit carrier, no Nat-to-unit calibration map, and no dimensional-preservation law are supplied.
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda:24-59`: external receipt fields require authority, physical unit carrier, Nat-to-unit map, quotient map, factorization, and dimensional-preservation witnesses.
- `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda:248-276`: first missing queue is accepted DY authority, W4 Z adequacy, external physical calibration receipt, matter field, stress-energy, and strict physical scale-setting.
- `DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda:65-110`: Candidate256 external receipt requires accepted DY authority, W4 Z adequacy receipt, Candidate256 authority, unit carrier, scale maps, calibration constant, dimensional preservation, citation, and validation payload.
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda:117-132`: provider request repeats the missing W4 external receipt fields and queue.
