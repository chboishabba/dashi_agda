module DASHI.Reasoning.RelationRepresentationFrontierProgressGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ObligationReducingExtensionGuardExact as Guard
import DASHI.Reasoning.RelationRepresentationCandidateDiscriminationExact as Candidate

------------------------------------------------------------------------
-- THIN #632 CONSUMER OF THE GENERIC CORE GUARD
--
-- The richer experiment language is admitted because it strictly refines the
-- old in-sample observer on actual candidate-family witnesses.  This is the
-- theorem-bearing reason to add the context/local-perturbation layer; merely
-- naming more representation families would remain scaffolding.
------------------------------------------------------------------------

oldCandidateObserver : Candidate.CandidateFamily → Candidate.ProbeOutcome
oldCandidateObserver candidate =
  Candidate.candidateOutcome candidate Candidate.inSampleFitProbe

newCandidateObserver :
  Candidate.CandidateFamily → Candidate.ProbeOutcome × Candidate.ProbeOutcome
newCandidateObserver candidate =
  Candidate.candidateOutcome candidate Candidate.heldOutContextProbe ,
  Candidate.candidateOutcome candidate Candidate.localPerturbationProbe

offsetAffineOldCollision :
  oldCandidateObserver Candidate.offsetCandidate ≡
  oldCandidateObserver Candidate.affineCandidate
offsetAffineOldCollision = refl

offsetAffineNewSeparation :
  newCandidateObserver Candidate.offsetCandidate ≡
  newCandidateObserver Candidate.affineCandidate → ⊥
offsetAffineNewSeparation ()

candidateExperimentRefinementReceipt :
  Guard.StrictObserverRefinementReceipt
    Candidate.CandidateFamily
    Candidate.ProbeOutcome
    (Candidate.ProbeOutcome × Candidate.ProbeOutcome)
    oldCandidateObserver
    newCandidateObserver
candidateExperimentRefinementReceipt =
  Guard.strictObserverRefinementReceipt
    Candidate.offsetCandidate
    Candidate.affineCandidate
    offsetAffineOldCollision
    offsetAffineNewSeparation

candidateExperimentExtensionAdmission : Guard.ExtensionAdmission
candidateExperimentExtensionAdmission =
  Guard.extensionAdmission
    "context + local-perturbation candidate-discrimination layer"
    (Guard.theoremBearingProgress
      (Guard.refined candidateExperimentRefinementReceipt))
    "offset/affine old collision plus richer-probe separation"
    "DASHI internal finite experiment-discrimination theorem"

candidateExperimentLayerIsPromotionRelevant :
  Guard.PromotionRelevant candidateExperimentExtensionAdmission
candidateExperimentLayerIsPromotionRelevant = tt

------------------------------------------------------------------------
-- By contrast, another naming/chart layer with no discharge, refinement or
-- exposure receipt remains explicitly non-promoting.
------------------------------------------------------------------------

representationVocabularyOnlyAdmission : Guard.ExtensionAdmission
representationVocabularyOnlyAdmission =
  Guard.extensionAdmission
    "representation vocabulary only"
    Guard.scaffoldingOnly
    "none"
    "internal naming layer"

representationVocabularyOnlyCannotPromote :
  Guard.PromotionRelevant representationVocabularyOnlyAdmission → ⊥
representationVocabularyOnlyCannotPromote ()

record RelationRepresentationFrontierProgressBoundary : Set where
  constructor relationRepresentationFrontierProgressBoundary
  field
    richerProbeLayerHasStrictRefinementReceipt : Bool
    richerProbeLayerHasStrictRefinementReceiptIsTrue :
      richerProbeLayerHasStrictRefinementReceipt ≡ true

    vocabularyOnlyLayerAdvancesFrontier : Bool
    vocabularyOnlyLayerAdvancesFrontierIsFalse :
      vocabularyOnlyLayerAdvancesFrontier ≡ false

canonicalRelationRepresentationFrontierProgressBoundary :
  RelationRepresentationFrontierProgressBoundary
canonicalRelationRepresentationFrontierProgressBoundary =
  relationRepresentationFrontierProgressBoundary
    true refl
    false refl
