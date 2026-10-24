module DASHI.Reasoning.LilaE6TitsExtensionExperimentHandoffExact where

------------------------------------------------------------------------
-- LILA EMPIRICAL HANDOFF: WEYL LABEL ACTION != LINEAR TITS-EXTENSION ACTION
--
-- Sibling exceptional branch PR #1106 now carries an execution-grade result on
-- the literal first-Tits 27 basis:
--
--   * E6 minuscule labels are transported to M3^3 basis labels;
--   * all six simple-reflection permutations preserve the 45-term cubic support;
--   * each has a signed monomial lift preserving every cubic coefficient;
--   * square/Coxeter residuals generate the full rank-6 diagonal 2-torsion
--     kernel (order 64) under Weyl conjugation;
--   * the resulting monomial Tits extension has order 64*51840=3317760;
--   * it is not promoted to a strict section of W(E6).
--
-- This owner does not import the sibling branch or promote Python execution to
-- kernel proof. It records the empirical consequence: LILA may match a finite
-- Weyl label permutation while failing the richer signed linear action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record LilaExceptionalActionEvidenceGrades : Set where
  constructor lila-exceptional-action-evidence-grades
  field
    weightLabelCount : Nat
    cubicMonomialCount : Nat
    simpleReflectionCount : Nat
    finiteWeylOrder : Nat
    diagonalTitsKernelOrder : Nat
    monomialTitsExtensionOrder : Nat
    finiteWeightPermutationFitRequired : Bool
    signedLinearLiftFitRequired : Bool
    cubicCompatibilityRequired : Bool
    diagonalTitsResidualTrackingRequired : Bool
    heldOutCompositionRequired : Bool
    decoderCompatibilityRequired : Bool
    permutationFitImpliesLinearActionFit : Bool
    linearActionFitImpliesMechanismIdentity : Bool
open LilaExceptionalActionEvidenceGrades public

canonicalLilaExceptionalActionEvidenceGrades :
  LilaExceptionalActionEvidenceGrades
canonicalLilaExceptionalActionEvidenceGrades =
  lila-exceptional-action-evidence-grades
    27 45 6 51840 64 3317760
    true true true true true true
    false false

record LilaE6TitsExtensionHandoffBoundary : Set where
  constructor lila-e6-tits-extension-handoff-boundary
  field
    siblingFirstTitsFiniteWeightBridgeReported : Bool
    siblingSignedCubicPreservingSimpleLiftsReported : Bool
    siblingFullDiagonalKernelReported : Bool
    siblingMonomialExtensionOrderReported : Bool
    siblingStrictWeylSectionReported : Bool
    lilaActualTrajectoryDataPresentHere : Bool
    lilaSameWeightPermutationActionEmpiricallyPaid : Bool
    lilaSameSignedLinearActionEmpiricallyPaid : Bool
    lilaHeldOutTitsCompositionEmpiricallyPaid : Bool
    note : String
open LilaE6TitsExtensionHandoffBoundary public

canonicalLilaE6TitsExtensionHandoffBoundary :
  LilaE6TitsExtensionHandoffBoundary
canonicalLilaE6TitsExtensionHandoffBoundary =
  lila-e6-tits-extension-handoff-boundary
    true true true true false
    false false false false
    "PR #1106 sharpens the E6 candidate from a 27-label Weyl permutation to a finite signed-monomial first-Tits Tits extension of order 3,317,760 with diagonal kernel 2^6. LILA experiments must therefore report label-action fit and signed linear-action fit separately, with cubic compatibility, residual/extension composition and decoder compatibility. No actual model trajectory is present here, so no empirical same-action promotion is made."
