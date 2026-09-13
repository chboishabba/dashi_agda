module DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Costed
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as SourceAdmission
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact as Diagnosis

------------------------------------------------------------------------
-- HIGHEST-ALPHA OBSERVATION CHOICE
--
-- "Highest alpha" is not a magic scalar.  It is a consumer-relative,
-- proof-search-admitted, non-dominated choice among declared candidates.  The
-- objective preserves expected prerequisite reduction, resource cost, privacy,
-- non-domination, retaliation/publication and authority burdens separately.
------------------------------------------------------------------------

record ObservationBurden : Set where
  constructor observation-burden
  field
    resourceCost : Nat
    privacyBurden : Nat
    nonDominationBurden : Nat
    retaliationPublicationBurden : Nat
    authorityBurden : Nat
    burdenCalibrationReference : String

open ObservationBurden public

record HighestAlphaCandidate : Set where
  constructor highest-alpha-candidate
  field
    concern : Diagnosis.DiagnosedWorldConcern
    worldResidual : Public.WorldQueryResidual
    informationMove : Costed.InformationMove
    sourceDiligence : SourceAdmission.SourceDiligence
    expectedPrerequisiteReductionReference : String
    exactMissingPrerequisiteReference : String
    observationCoordinateReference : String
    burden : ObservationBurden
    leastIntrusiveAlternativeAuditReference : String
    acquisitionAuthorityReference : String
    publicationSafetyReference : String
    downstreamActionAuthoritySeparateReference : String

open HighestAlphaCandidate public

-- Applications supply the semantic Pareto relation.  Keeping it external avoids
-- silently asserting that incomparable ethical/epistemic dimensions collapse to
-- one universal arithmetic utility.
record HighestAlphaChoice
    (Declared : HighestAlphaCandidate → Set)
    (Pays : HighestAlphaCandidate → Set)
    (StrictlyDominates : HighestAlphaCandidate → HighestAlphaCandidate → Set) : Set₁ where
  constructor highest-alpha-choice
  field
    selected : HighestAlphaCandidate
    selectedDeclared : Declared selected
    selectedPays : Pays selected
    proofSearchAdmission : ProofSearch.RouteAdmission
    noDeclaredPayingCandidateStrictlyDominates :
      (alternative : HighestAlphaCandidate) →
      Declared alternative →
      Pays alternative →
      StrictlyDominates alternative selected →
      ⊥
    comparisonSetReference : String
    dominancePolicyReference : String

open HighestAlphaChoice public

------------------------------------------------------------------------
-- Existing least-cost actionability owner remains available as one projection.
------------------------------------------------------------------------

record CostProjectionBridge : Set where
  constructor cost-projection-bridge
  field
    candidate : HighestAlphaCandidate
    costedMove : Costed.InformationMove
    sameMoveReference : String
    costProjectionIsWholeEthicalOrdering : Bool
    costProjectionIsWholeEthicalOrderingIsFalse :
      costProjectionIsWholeEthicalOrdering ≡ false

------------------------------------------------------------------------
-- Fail-closed authority boundaries.
------------------------------------------------------------------------

data HighestInformationGainCreatesAcquisitionAuthority : Set where
data LeastIntrusiveAutomaticallyMeansHighestAlpha : Set where
data SelectedObservationCreatesFact : Set where
data ParetoChoiceCreatesInterventionAuthority : Set where

highestInformationGainDoesNotCreateAcquisitionAuthority :
  HighestInformationGainCreatesAcquisitionAuthority → ⊥
highestInformationGainDoesNotCreateAcquisitionAuthority ()

leastIntrusiveDoesNotAutomaticallyMeanHighestAlpha :
  LeastIntrusiveAutomaticallyMeansHighestAlpha → ⊥
leastIntrusiveDoesNotAutomaticallyMeanHighestAlpha ()

selectedObservationDoesNotCreateFact : SelectedObservationCreatesFact → ⊥
selectedObservationDoesNotCreateFact ()

paretoChoiceDoesNotCreateInterventionAuthority :
  ParetoChoiceCreatesInterventionAuthority → ⊥
paretoChoiceDoesNotCreateInterventionAuthority ()

record HighestAlphaObservationBoundary : Set where
  constructor highest-alpha-observation-boundary
  field
    sourceDiligenceIsPartOfCandidate : Bool
    sourceDiligenceIsPartOfCandidateIsTrue : sourceDiligenceIsPartOfCandidate ≡ true
    ethicalEpistemicDimensionsNeedNotCollapseToOneScalar : Bool
    ethicalEpistemicDimensionsNeedNotCollapseToOneScalarIsTrue :
      ethicalEpistemicDimensionsNeedNotCollapseToOneScalar ≡ true
    proofSearchAdmissionRemainsRequired : Bool
    proofSearchAdmissionRemainsRequiredIsTrue : proofSearchAdmissionRemainsRequired ≡ true
    selectionIsEvidenceAcquisitionNotTruthPromotion : Bool
    selectionIsEvidenceAcquisitionNotTruthPromotionIsTrue :
      selectionIsEvidenceAcquisitionNotTruthPromotion ≡ true

canonicalHighestAlphaObservationBoundary : HighestAlphaObservationBoundary
canonicalHighestAlphaObservationBoundary =
  highest-alpha-observation-boundary true refl true refl true refl true refl
