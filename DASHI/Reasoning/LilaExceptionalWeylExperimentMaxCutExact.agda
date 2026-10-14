module DASHI.Reasoning.LilaExceptionalWeylExperimentMaxCutExact where

------------------------------------------------------------------------
-- LILA / TELEODYNAMICS EXCEPTIONAL-WEYL MAX-CUT
--
-- This branch already owns the model-facing semantic-action / LILA experiment
-- machinery. Stronger sibling exceptional branches now own substantially more
-- finite and algebraic structure than an earlier "find a Weyl action" roadmap
-- suggested:
--
--   PR #1098 / Lean #47 / Lean #58:
--     * same-action W(E6) / minuscule-27 / Schlaefli geometry;
--     * literal six-lift four-space closure order 103680;
--     * primitive exterior-square kernel {+I,-I}, order 2;
--     * projective quotient order 51840, with the existing five-space word
--       action agreeing with the repo E6 action;
--     * folded W(F4), exact F4 root datum;
--     * intrinsic structured E8 Cartan/Coxeter/root datum;
--     * original punctured T5 natural-E6 recognition obstruction.
--
--   The projectivization receipt is stronger than an order coincidence but is
--   deliberately NOT recorded as an abstract PGSp4(3) ~= W(E6) theorem.
--
--   PR #1106 / Lean #52:
--     * literal first-Tits M3^3 27-dimensional carrier and cubic;
--     * E6 norm-symmetry / F4 unit-stabilizer diagnostics;
--     * signed monomial E6 simple lifts and Tits-extension residuals;
--     * native Albert / Spin-triality / derivation-F4 programme.
--
--   PR #1124 / Lean #64 (superseding stale Lean #60):
--     * scoped deterministic validators and artifact future-sufficiency;
--     * consumer-relative verifier sufficiency / observer non-descent.
--
--   PR #1121:
--     * Brain-IT fMRI observation/transfer donor with explicit lossy-observer
--       and no-universal-latent-inversion boundary.
--
-- Cross-branch facts below are receipts, not imported Agda kernel theorems.
-- The local E6 Tits handoff is imported directly and therefore distinguished.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.LilaE6TitsExtensionExperimentHandoffExact as Tits

------------------------------------------------------------------------
-- 1. Evidence grades for a model-facing exceptional symmetry experiment.
------------------------------------------------------------------------

record WeylModelEvidenceLadder : Set where
  constructor weyl-model-evidence-ladder
  field
    rootOrWeightCarrierAvailable : Bool
    invariantGeometryAvailable : Bool
    generatorActionAvailable : Bool
    coxeterCompositionAvailable : Bool
    sameObjectActionIntertwinerAvailable : Bool
    signedLinearLiftAvailable : Bool
    heldOutWordEvaluationRequired : Bool
    decoderCompatibilityRequired : Bool
    futureConsumerEvaluationRequired : Bool
    fitCreatesMechanismIdentity : Bool
    fitCreatesPhenomenalIdentity : Bool
open WeylModelEvidenceLadder public

canonicalWeylModelEvidenceLadder : WeylModelEvidenceLadder
canonicalWeylModelEvidenceLadder =
  weyl-model-evidence-ladder
    true true true true true true
    true true true
    false false

------------------------------------------------------------------------
-- 2. Current paid mathematical candidates.
------------------------------------------------------------------------

record ExceptionalCandidateInventory : Set where
  constructor exceptional-candidate-inventory
  field
    e6WeightCount : Nat
    e6FiniteWeylOrder : Nat
    e6FourSpaceClosureOrder : Nat
    e6ExteriorSquareKernelOrder : Nat
    e6ProjectiveQuotientOrder : Nat
    e6PGSpProjectivizationDonorReported : Bool
    abstractPGSp4IsomorphicWE6Paid : Bool
    f4RootCount : Nat
    f4FiniteWeylOrder : Nat
    structuredE8RootCount : Nat
    structuredE8ExpectedWeylOrder : Nat
    localE6TitsKernelOrder : Nat
    localE6TitsExtensionOrder : Nat
    e6MinusculeSameActionDonorReported : Bool
    f4FoldedCoxeterDonorReported : Bool
    structuredE8RootDatumDonorReported : Bool
    firstTitsSignedLinearDonorReported : Bool
    originalT5NaturalE6RouteBlockedInDonor : Bool
    siblingFactsAreLocalKernelImports : Bool
open ExceptionalCandidateInventory public

canonicalExceptionalCandidateInventory : ExceptionalCandidateInventory
canonicalExceptionalCandidateInventory =
  exceptional-candidate-inventory
    27 51840
    103680 2 51840 true false
    48 1152
    240 696729600
    (Tits.diagonalTitsKernelOrder Tits.canonicalLilaExceptionalActionEvidenceGrades)
    (Tits.monomialTitsExtensionOrder Tits.canonicalLilaExceptionalActionEvidenceGrades)
    true true true true true
    false

------------------------------------------------------------------------
-- 3. LILA experiment protocol after reusing the actual Weyl machinery.
------------------------------------------------------------------------

record LilaExceptionalWeylExperimentProtocol : Set where
  constructor lila-exceptional-weyl-experiment-protocol
  field
    comparePlainBaseline : Bool
    compareRandomMatchedPrior : Bool
    compareE6MinusculeWeightPrior : Bool
    compareF4FoldedPrior : Bool
    compareStructuredE8Prior : Bool
    compareLearnedUnconstrainedPrior : Bool
    measureRootOrWeightOccupancy : Bool
    measureGeneratorFit : Bool
    measureCoxeterResidual : Bool
    measureSignedLinearLiftFit : Bool
    measureTitsKernelResidual : Bool
    measureHeldOutWeylWords : Bool
    measureDecoderCompatibility : Bool
    measureFutureConsumerLanguage : Bool
    keepSameParameterBudget : Bool
    keepSameOptimizerAndSeeds : Bool
    predeclareTrainHoldoutWords : Bool
open LilaExceptionalWeylExperimentProtocol public

canonicalLilaExceptionalWeylExperimentProtocol :
  LilaExceptionalWeylExperimentProtocol
canonicalLilaExceptionalWeylExperimentProtocol =
  lila-exceptional-weyl-experiment-protocol
    true true true true true true
    true true true true true true true true
    true true true

------------------------------------------------------------------------
-- 4. Productive cross-pollinations.
------------------------------------------------------------------------

record ScopedVerifierWeylCrossPollination : Set where
  constructor scoped-verifier-weyl-cross-pollination
  field
    siblingScopedVerifierArchitectureAvailable : Bool
    generatorClaimCanBeScopedSeparately : Bool
    coxeterClaimCanBeScopedSeparately : Bool
    heldOutWordClaimCanBeScopedSeparately : Bool
    outOfDomainStatusRequired : Bool
    oneVerifiedGeneratorImpliesWholeGroupVerified : Bool
open ScopedVerifierWeylCrossPollination public

canonicalScopedVerifierWeylCrossPollination :
  ScopedVerifierWeylCrossPollination
canonicalScopedVerifierWeylCrossPollination =
  scoped-verifier-weyl-cross-pollination
    true true true true true false

record BrainITExceptionalObservationCrossPollination : Set where
  constructor brain-it-exceptional-observation-cross-pollination
  field
    siblingBrainITObservationDonorAvailable : Bool
    fMRIIsLossyObservationChannel : Bool
    exceptionalFeatureMapMustBePredeclared : Bool
    heldOutSubjectOrCheckpointRequired : Bool
    nuisanceControlsRequired : Bool
    reconstructionSuccessImpliesExceptionalLatentMechanism : Bool
    exceptionalLatentFitImpliesConsciousnessIdentity : Bool
open BrainITExceptionalObservationCrossPollination public

canonicalBrainITExceptionalObservationCrossPollination :
  BrainITExceptionalObservationCrossPollination
canonicalBrainITExceptionalObservationCrossPollination =
  brain-it-exceptional-observation-cross-pollination
    true true true true true false false

------------------------------------------------------------------------
-- 5. Consolidated max-cut / authority boundary.
------------------------------------------------------------------------

record LilaExceptionalWeylMaxCut : Set where
  constructor lila-exceptional-weyl-max-cut
  field
    existingWeylMachineryReused : Bool
    e6MinusculeSameActionPaidInDonor : Bool
    structuredE8RootDatumPaidInDonor : Bool
    f4FiniteWeylPaidInDonor : Bool
    firstTitsSignedLinearExtensionPaidInDonor : Bool
    localTitsHandoffImported : Bool
    originalT5NaturalE6RecognitionPaid : Bool
    rootCodebookImpliesModelEquivariance : Bool
    generatorFitImpliesHeldOutWordFit : Bool
    finiteWeylImpliesContinuousExceptionalGroup : Bool
    siblingReceiptCountsAsLocalKernelProof : Bool
    actualLilaTrajectoryActionFitPaid : Bool
    actualNeuralExceptionalActionFitPaid : Bool
    scopedVerifierEmpiricalReceiptsPaid : Bool
    note : String
open LilaExceptionalWeylMaxCut public

canonicalLilaExceptionalWeylMaxCut : LilaExceptionalWeylMaxCut
canonicalLilaExceptionalWeylMaxCut =
  lila-exceptional-weyl-max-cut
    true true true true true true
    false
    false false false false
    false false false
    "The repo already owns the relevant finite Weyl/root/action machinery on the exceptional branches, now including the literal four-space closure 103680, exterior-square kernel {+I,-I}, and projective quotient 51840 on Lean #58. That projectivization strengthens the same-action provenance without manufacturing an abstract PGSp4(3) ~= W(E6) theorem. The live frontier is same-model empirical intertwining: generator fit, Coxeter/Tits residuals, held-out Weyl words, decoder compatibility, future-consumer behaviour, and consumer-relative scoped validation on actual LILA/neural trajectories. Sibling-branch facts remain receipts until histories are reconciled or imports land on one branch."
