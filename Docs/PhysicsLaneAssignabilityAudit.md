# Physics Lane Assignability Audit

Date: `2026-05-12`
Owner: `Noether`
Scope: W1-W6 physics-lane assignability from local docs and typed receipts.

This audit is docs-only and non-promoting. It does not construct authority
tokens, receipts, runtime payloads, calibration artifacts, Brain-lane support,
or any unification claim.

## Summary Table

| Lane | Worker / name present locally | Current blocker status | Assignable now? | Typed kill condition or first-missing | Brain lateral-support proviso inactive? |
| --- | --- | --- | --- | --- | --- |
| `W1` MDL/CR final seam | `Noether`; K-row `K1-W1-final-seam` | Kill matrix marks `W1MdlCr` `unblocked`; final retargeted seam receipt and downstream handoff are recorded as landed for the kill condition. Old current-carrier CR-flatness remains obstructed and must not be revived. | No active blocker assignment needed. Only assign if a new downstream consumer is explicitly scoped. | Kill condition: `RetargetedFinalSeamReceiptFields` with `W1KillAuthority` and `W1KillEvidence`; `BlockerKillConditions.w1KillCondition.currentState = unblocked`. | Yes. Brain receipts are non-promoting and supply no W1 seam authority. |
| `W2` natural / p2 convergence | `Newton` / `Hooke`, `Newton` / `Feynman`, earlier `Turing`; K-row `K2-W2-natural-p2` | Blocked. Local normalizeAdd and shift-flow support exist, but the promotion receipt eliminates through the constructorless `NaturalP2ConvergencePromotionAuthorityToken`; no legitimate constructor or policy hook is present. | Not assignable to another internal closure/proof worker. Assignable only as governance/external-authority or impossibility-sharpening work if policy changes. | First missing: `NaturalP2ConvergencePromotionAuthorityToken`; full missing list also includes natural bridge/obstruction, naturality/coherence, carrier transport, carrier-general convergence, realization uniformity, and offline-L2 lift fields. Kill condition: `NaturalP2ConvergencePromotionReceipt` plus `W2KillAuthority` and `W2KillEvidence`. | Yes. Brain receipts do not activate W2 promotion authority or p2 convergence support. |
| `W3` empirical accepted authority | `Curie-W3` / `Curie`, `Curie-W3` / `Hypatia`, `Curie-W3` / `Lorentz`; K-row `K3-W3-empirical-authority` | Blocked. The packet and provider-facing handoff are ready, but no accepted external `W3AcceptedEvidenceAuthorityToken` or `W3AcceptedAuthorityExternalReceipt` exists locally. | Not assignable to internal proof closure. Assignable only to external provider-response intake or to a typed rejected/insufficient authority diagnostic. | First missing: `W3AcceptedEvidenceAuthorityToken`. Request-pack missing fields also include evidence-backed target, target-authority equality, B4 empirical promotion, origin receipt promotion, bridge obligations, and bridge-target equality. Kill condition: `W3AcceptedAuthorityExternalReceipt` plus token match and evidence-authority match. | Yes. Brain receipts are explicitly non-promoting and cannot supply W3 empirical authority. |
| `W4` calibration / chemistry / matter source | `Faraday` / `Boole`; `Laplace` / `Copernicus`; `Kelvin` / `Halley`; `Hypatia-Faraday` / `Peirce`; `Gauss-Noether` / `Gibbs`; K-row `K4-W4-calibration` | Blocked. The dirty Z-peak run is locally wired but inadequate (`chi2/dof = 298.8462841768543`). W4 remains downstream of accepted DY luminosity convention, `W4ZAdequacy`, and `Candidate256PhysicalCalibrationExternalReceipt`; the physical calibration authority is constructorless locally. | Assignable only for external DY/provider response, fail-closed adequacy computation under accepted inputs, or request/diagnostic sharpening. Not assignable for local promotion. | First missing: `missingAcceptedDYLuminosityConventionAuthority`, followed by `missingW4ZAdequacy`, `missingExternalPhysicalCalibrationReceipt`, `missingMatterFieldFromW4`, and `missingStressEnergyTensorFromW4`. Kill condition: `Candidate256PhysicalCalibrationExternalReceipt` with matching `Candidate256PhysicalCalibrationAuthorityToken` and physical-unit evidence. | Yes. Brain receipts do not activate W4 calibration, physical units, chemistry promotion, or stress-energy. |
| `W5` GRQFT / PDF consumer | `Maxwell` / `Boyle`; `Feynman` / `Volta`; `Maxwell-GRQFT` / `Averroes`; K-row `K5-W5-grqft` | Blocked. The request pack names the required GRQFT closure-promotion payload, but no promotion authority, external PDF carrier prerequisite, GR law, QFT law, consumer witnesses, empirical validation, or closure-promotion receipt exists. | Assignable only to external GRQFT/PDF provider-response intake or a typed first-missing diagnostic. Not assignable for local closure promotion. | First missing policy starts at `firstMissingGRQFTClosurePromotionAuthorityToken`; missing receipt fields are `missingPromotionAuthorityToken`, `missingPDFCarrierPrerequisite`, `missingGREquationLaw`, `missingGREquationLawAtConsumer`, `missingQFTInteractionLaw`, `missingQFTInteractionLawAtConsumer`, and `missingEmpiricalGRQFTValidation`. Kill condition: `GRQFTClosurePromotionReceipt` plus `W5KillAuthority` and `W5KillEvidence`. | Yes. Brain receipts provide no W5 PDF carrier, GR/QFT law, empirical GRQFT validation, or closure-promotion authority. |
| `W6` ITIR / PNF runtime consumer | `Liskov` plus `Hopper` plus `Ada`; K-row `K6-W6-pnf-runtime` | Blocked. Constructors and request surfaces exist, but no concrete runtime payload is present: consumer profile/id, paired `PNFEmissionReceipt`s, receipt-backed residual computation, and Hecke candidate-pool receipt id are absent. | Yes, but only as runtime/provider payload collection or fixture wiring after real receipt values exist. Not assignable to label-by-inspection or synthetic runtime receipt construction. | First missing: concrete runtime payload fields: `missingConcreteConsumerProfileValue`, `missingConcreteRuntimeReceiptIdValue`, `missingConcreteLeftPNFEmissionReceiptValue`, `missingConcreteRightPNFEmissionReceiptValue`, `missingConcreteReceiptBackedResidualComputation`, and `missingConcreteHeckeCandidatePoolReceiptIdValue`. Kill condition: `PNFResidualConsumerReceipt` plus runtime receipt authority acknowledgement. | Yes. Brain receipts do not supply PNF runtime receipts, residual computation, or Hecke candidate-pool receipt ids. |

## Assignability Notes

- `W1` is the only W1-W6 lane with a locally unblocked kill condition. It should
  not receive another blocker worker unless the assignment is a new downstream
  consumer, not a re-opening of the old current-carrier route.
- `W2`, `W3`, `W4`, and `W5` are blocked by constructorless or external
  authority/provenance gates. Their admissible work is provider intake,
  governance decision, request-pack refinement, or typed insufficiency/rejection
  diagnostics.
- `W6` remains assignable to a runtime/provider payload lane because the local
  builder can construct `PNFResidualConsumerReceipt` after real runtime receipt
  values are supplied. The current repo does not supply those values.
- The Brain lateral-support proviso is inactive for every W1-W6 lane audited
  here. Local Brain surfaces are adjacent and non-promoting; selected
  dashiBRAIN receipts record single-scale numeric evidence and a multiscale
  persistence obstruction, but they do not promote physics closure, empirical
  adequacy, biological recovery, or unification.

## Evidence Sources

- `Docs/WorkerCoordinationBoard.md`: current active rounds, worker names,
  first-missing summaries, and non-promotion governance.
- `TODO.md`: active blocker board, K1-K6 kill rows, current-lane maturity table,
  and W6 runtime-provider attempt status.
- `DASHI/Physics/Closure/BlockerKillConditions.agda`: receipt-driven kill
  matrix for W1-W6 and typed promotion targets.
- `DASHI/Physics/Closure/CanonicalToNoncanonicalMdlRetargetFinalSeamObligation.agda`:
  W1 final seam receipt fields and landed status.
- `DASHI/Physics/Closure/NaturalP2ConvergencePromotionObligation.agda`,
  `DASHI/Physics/Closure/W2PromotionAuthorityReceipt.agda`, and
  `DASHI/Physics/Closure/W2GovernanceSelfIssuanceIntakeRequest.agda`: W2
  constructorless authority and remaining missing fields.
- `DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda`,
  `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptObligation.agda`,
  `DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenReceipt.agda`, and
  `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda`:
  W3 authority-token and external-receipt blockers.
- `DASHI/Physics/Closure/W4ZAdequacyReceipt.agda`,
  `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda`,
  `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda`,
  and `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda`:
  W4 accepted-DY, adequacy, and Candidate256 calibration blockers.
- `DASHI/Physics/Closure/GRQFTConsumerNextObligation.agda`,
  `DASHI/Physics/Closure/GRQFTConsumerSourceDiagnostic.agda`, and
  `DASHI/Physics/Closure/GRQFTClosurePromotionReceiptRequestPack.agda`: W5
  GRQFT closure-promotion blockers.
- `DASHI/Interop/PNFResidualConsumerNextObligation.agda`,
  `DASHI/Interop/PNFResidualConsumerReceiptRequestPack.agda`,
  `DASHI/Interop/PNFResidualConsumerRuntimeProviderAttempt.agda`, and
  `Docs/ITIRPNFResidualLogicBridge.md`: W6 runtime receipt and PNF residual
  consumer blockers.
- `Docs/BrainLaneStatus.md` and `Docs/DrosophilaHemibrainArtifactManifest.md`:
  Brain lane adjacency, non-promotion boundary, selected external numeric
  receipts, and multiscale persistence obstruction.
