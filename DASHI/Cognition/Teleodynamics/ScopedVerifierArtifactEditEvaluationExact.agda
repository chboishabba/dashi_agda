module DASHI.Cognition.Teleodynamics.ScopedVerifierArtifactEditEvaluationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.Teleodynamics.ScopedVerifierArchitectureExact as Verify
import DASHI.Cognition.Teleodynamics.VerifiedArtifactTransitionExact as Artifact
import DASHI.Cognition.Teleodynamics.ArtifactFutureSufficiencyExact as Future
import DASHI.Cognition.Teleodynamics.ScopedVerifierSameObjectEvaluationExact as Eval

------------------------------------------------------------------------
-- ARTIFACT EDIT × FUTURE SUFFICIENCY × SAME-OBJECT HELD-OUT EVALUATION
--
-- The artifact-transition owner already pays identity preservation, declared
-- edit semantics, residual reopening and before/after validation.  The future
-- owner separately pays reconstruction/future-observation sufficiency.  The
-- same-object evaluation owner separately pays eligible candidate/baseline,
-- same case/intervention and held-out protocol obligations.
--
-- This owner only composes those receipts.  It does not let deterministic
-- replay, post-edit validator success or future sufficiency substitute for an
-- empirical held-out comparison.
------------------------------------------------------------------------

record ArtifactEditHeldOutEvaluation
    {Identity Body Residual X O₁ O₂ C Intervention : Set}
    (V : Verify.ScopedValidator (Artifact.ArtifactState Identity Body Residual))
    (M : Future.ArtifactFutureModel Body Residual)
    (before after : Artifact.ArtifactState Identity Body Residual)
    (candidateObserve : X → O₁)
    (baselineObserve : X → O₂)
    (consumer : X → C) : Set₁ where
  constructor artifact-edit-held-out-evaluation
  field
    transition : Artifact.VerifiedArtifactTransition V before after
    futureSufficiency : Future.ResidualFutureSufficiency M after
    evaluation : Eval.SameObjectHeldOutEvaluation
      candidateObserve baselineObserve consumer Identity Intervention
    candidateCaseMatchesBefore :
      Eval.candidateCase evaluation ≡ Artifact.identity before
    baselineCaseMatchesAfter :
      Eval.baselineCase evaluation ≡ Artifact.identity after

open ArtifactEditHeldOutEvaluation public

editPreservesArtifactIdentity :
  ∀ {Identity Body Residual X O₁ O₂ C Intervention : Set}
    {V : Verify.ScopedValidator (Artifact.ArtifactState Identity Body Residual)}
    {M : Future.ArtifactFutureModel Body Residual}
    {before after : Artifact.ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C} →
  ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer →
  Artifact.identity before ≡ Artifact.identity after
editPreservesArtifactIdentity r = Artifact.sameArtifactIdentity (transition r)

heldOutCasesTrackSameArtifact :
  ∀ {Identity Body Residual X O₁ O₂ C Intervention : Set}
    {V : Verify.ScopedValidator (Artifact.ArtifactState Identity Body Residual)}
    {M : Future.ArtifactFutureModel Body Residual}
    {before after : Artifact.ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C} →
  (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) →
  Eval.candidateCase (evaluation r) ≡ Eval.baselineCase (evaluation r)
heldOutCasesTrackSameArtifact r = Eval.sameCase (evaluation r)

candidateHeldOutCaseIsPostEditIdentity :
  ∀ {Identity Body Residual X O₁ O₂ C Intervention : Set}
    {V : Verify.ScopedValidator (Artifact.ArtifactState Identity Body Residual)}
    {M : Future.ArtifactFutureModel Body Residual}
    {before after : Artifact.ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C} →
  (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) →
  Eval.candidateCase (evaluation r) ≡ Artifact.identity after
candidateHeldOutCaseIsPostEditIdentity r =
  trans (candidateCaseMatchesBefore r) (Artifact.sameArtifactIdentity (transition r))
  where
    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl refl = refl

record ArtifactEditEvaluationBoundary : Set where
  constructor artifact-edit-evaluation-boundary
  field
    sameArtifactIdentityRequired : Bool
    declaredEditSemanticsRequired : Bool
    postEditValidationRequired : Bool
    futureSufficiencyRequired : Bool
    sameObjectHeldOutEvaluationRequired : Bool
    editReplayAloneCountsAsEvaluation : Bool
    futureSufficiencyAloneCountsAsEmpiricalWin : Bool
    validatorPassAloneCountsAsArtifactIdentity : Bool

open ArtifactEditEvaluationBoundary public

canonicalArtifactEditEvaluationBoundary : ArtifactEditEvaluationBoundary
canonicalArtifactEditEvaluationBoundary =
  artifact-edit-evaluation-boundary
    true true true true true false false false
