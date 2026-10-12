module DASHI.Reasoning.LilaE6TitsExtensionExperimentHandoffExact where

------------------------------------------------------------------------
-- LILA EMPIRICAL HANDOFF: WEYL LABEL ACTION != LINEAR TITS-EXTENSION ACTION
--
-- Sibling exceptional branch PR #1106 now carries an execution-grade result on
-- the literal first-Tits 27 basis:
--
--   * the E6 minuscule 27 label action is transported to M3^3 basis labels;
--   * all six true simple-reflection permutations preserve the support of the
--     45-term first-Tits cubic;
--   * each admits an explicit signed monomial lift preserving every cubic
--     coefficient exactly;
--   * selected lifts need not give a strict W(E6) section: squares/Coxeter
--     words can carry diagonal cubic-preserving 2-torsion, i.e. the appropriate
--     Weyl-normalizer/Tits-extension surface.
--
-- This owner does not import that sibling branch or promote it to kernel proof.
-- It records the productive empirical consequence for LILA: a model can match
-- the finite Weyl LABEL permutation while failing the richer linear action.
-- Held-out experiments should therefore distinguish these evidence grades.
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
    27 45 6
    true true true true true true
    false false

record LilaE6TitsExtensionHandoffBoundary : Set where
  constructor lila-e6-tits-extension-handoff-boundary
  field
    siblingFirstTitsFiniteWeightBridgeReported : Bool
    siblingSignedCubicPreservingSimpleLiftsReported : Bool
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
    true true false
    false false false false
    "PR #1106 sharpens the E6 candidate from a 27-label Weyl permutation to signed monomial first-Tits cubic-preserving lifts with nontrivial Tits-extension residuals. This branch therefore requires LILA experiments to report label-action fit and linear signed-action fit separately, with held-out composition and decoder compatibility. No model trajectory is present here, so no empirical same-action promotion is made."
