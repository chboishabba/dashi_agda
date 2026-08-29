module DASHI.Reasoning.RelationRepresentationCandidateDiscriminationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy

------------------------------------------------------------------------
-- CANDIDATE-FAMILY DISCRIMINATION
--
-- Cross-pollination motivation:
--   * #636: theories are equivalent only relative to a declared experiment
--     language; a richer admissible measurement can split the equivalence;
--   * #624: candidate direction != action authorization / full viability;
--   * #632: translation, rotation, affine and contextual transforms are
--     competing representation families, not a truth ordering.
--
-- This local finite specimen remains independent of draft #636. Once #636 is
-- merged, the intended implementation is a thin adapter to the generic
-- experiment-language equivalence owner rather than a second calculus.
------------------------------------------------------------------------

data CandidateFamily : Set where
  offsetCandidate
  rotationCandidate
  affineCandidate
  contextualCandidate
  : CandidateFamily

data ExperimentProbe : Set where
  inSampleFitProbe
  heldOutTargetProbe
  heldOutContextProbe
  localPerturbationProbe
  : ExperimentProbe

data ProbeOutcome : Set where
  pass fail : ProbeOutcome

candidateOutcome : CandidateFamily → ExperimentProbe → ProbeOutcome
candidateOutcome offsetCandidate inSampleFitProbe = pass
candidateOutcome rotationCandidate inSampleFitProbe = pass
candidateOutcome affineCandidate inSampleFitProbe = pass
candidateOutcome contextualCandidate inSampleFitProbe = pass

candidateOutcome offsetCandidate heldOutTargetProbe = pass
candidateOutcome rotationCandidate heldOutTargetProbe = pass
candidateOutcome affineCandidate heldOutTargetProbe = pass
candidateOutcome contextualCandidate heldOutTargetProbe = pass

candidateOutcome offsetCandidate heldOutContextProbe = fail
candidateOutcome rotationCandidate heldOutContextProbe = fail
candidateOutcome affineCandidate heldOutContextProbe = pass
candidateOutcome contextualCandidate heldOutContextProbe = pass

candidateOutcome offsetCandidate localPerturbationProbe = fail
candidateOutcome rotationCandidate localPerturbationProbe = pass
candidateOutcome affineCandidate localPerturbationProbe = pass
candidateOutcome contextualCandidate localPerturbationProbe = pass

------------------------------------------------------------------------
-- Experiment-language equivalence is consumer/probe-relative.
------------------------------------------------------------------------

EquivalentUnder : ExperimentProbe → CandidateFamily → CandidateFamily → Set
EquivalentUnder probe left right =
  candidateOutcome left probe ≡ candidateOutcome right probe

allFamiliesEquivalentOnInSampleFit :
  (candidate : CandidateFamily) →
  EquivalentUnder inSampleFitProbe offsetCandidate candidate
allFamiliesEquivalentOnInSampleFit offsetCandidate = refl
allFamiliesEquivalentOnInSampleFit rotationCandidate = refl
allFamiliesEquivalentOnInSampleFit affineCandidate = refl
allFamiliesEquivalentOnInSampleFit contextualCandidate = refl

allFamiliesEquivalentOnHeldOutTarget :
  (candidate : CandidateFamily) →
  EquivalentUnder heldOutTargetProbe offsetCandidate candidate
allFamiliesEquivalentOnHeldOutTarget offsetCandidate = refl
allFamiliesEquivalentOnHeldOutTarget rotationCandidate = refl
allFamiliesEquivalentOnHeldOutTarget affineCandidate = refl
allFamiliesEquivalentOnHeldOutTarget contextualCandidate = refl

heldOutContextSeparatesOffsetFromAffine :
  EquivalentUnder heldOutContextProbe offsetCandidate affineCandidate → ⊥
heldOutContextSeparatesOffsetFromAffine ()

localPerturbationSeparatesOffsetFromRotation :
  EquivalentUnder localPerturbationProbe offsetCandidate rotationCandidate → ⊥
localPerturbationSeparatesOffsetFromRotation ()

------------------------------------------------------------------------
-- Minimal experimental reading for the motivating Instagram experiments.
-- A strong in-sample SVD/offset fit cannot choose the transformation family.
-- Context and local-perturbation probes are examples of richer measurements
-- that can separate families in this finite specimen.
------------------------------------------------------------------------

record CandidateDiscriminationBoundary : Set where
  constructor candidateDiscriminationBoundary
  field
    inSampleFitSelectsUniqueFamily : Bool
    inSampleFitSelectsUniqueFamilyIsFalse :
      inSampleFitSelectsUniqueFamily ≡ false

    heldOutTargetAloneSelectsUniqueFamily : Bool
    heldOutTargetAloneSelectsUniqueFamilyIsFalse :
      heldOutTargetAloneSelectsUniqueFamily ≡ false

    richerContextProbeMaySplitCandidates : Bool
    richerContextProbeMaySplitCandidatesIsTrue :
      richerContextProbeMaySplitCandidates ≡ true

    localPerturbationMaySplitOffsetFromOperator : Bool
    localPerturbationMaySplitOffsetFromOperatorIsTrue :
      localPerturbationMaySplitOffsetFromOperator ≡ true

    bestFitFamilyIsSemanticRealization : Bool
    bestFitFamilyIsSemanticRealizationIsFalse :
      bestFitFamilyIsSemanticRealization ≡ false

    directStage67AdapterPreferredAfterMerge : Bool
    directStage67AdapterPreferredAfterMergeIsTrue :
      directStage67AdapterPreferredAfterMerge ≡ true

canonicalCandidateDiscriminationBoundary : CandidateDiscriminationBoundary
canonicalCandidateDiscriminationBoundary =
  candidateDiscriminationBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
