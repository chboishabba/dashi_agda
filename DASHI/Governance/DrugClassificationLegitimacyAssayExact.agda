module DASHI.Governance.DrugClassificationLegitimacyAssayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.FeministDrugClassificationAuthorityExact as FeministDrug
import DASHI.Governance.DrugClassificationAsymmetryDiscriminatorExact as Classify
import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical

------------------------------------------------------------------------
-- DRUG CLASSIFICATION LEGITIMACY ASSAY
--
-- A classifier can successfully impose a route while failing on distinct
-- legitimacy coordinates.  Effectiveness of classification is therefore not
-- identified with epistemic, clinical, democratic, situated or sovereign
-- legitimacy.
------------------------------------------------------------------------

data LegitimacyAxis : Set where
  empiricalAdequacyAxis
  clinicalJustificationAxis
  affectedSubjectVoiceAxis
  affectedCommunityVoiceAxis
  democraticMandateAxis
  proceduralContestabilityAxis
  historicalRepairAxis
  indigenousSovereigntyAxis
  : LegitimacyAxis

data AxisStatus : Set where
  satisfied
  missing
  contested
  unresolved
  notApplicable
  : AxisStatus

record ClassificationLegitimacyProfile : Set where
  constructor classificationLegitimacyProfile
  field
    issuer : FeministDrug.CategoryIssuer
    category : FeministDrug.DrugCategory
    route : Classify.GovernanceCone
    statusAt : LegitimacyAxis → AxisStatus
    classifierVersion : Historical.ClassifierVersion
    sourceReference : String
    contestabilityReference : String

open ClassificationLegitimacyProfile public

------------------------------------------------------------------------
-- Synthetic finite regressions: same imposed route can hide different
-- legitimacy profiles.
------------------------------------------------------------------------

data LegitimacyState : Set where
  coercivelyImposedPunitiveState
  procedurallyReviewedPunitiveState
  : LegitimacyState

data ImposedRouteSurface : Set where
  samePunitiveRoute : ImposedRouteSurface

data LegitimacyCode : Set where
  coerciveLowLegitimacyCode
  reviewedContestableCode
  : LegitimacyCode

imposedRouteObserver : LegitimacyState → ImposedRouteSurface
imposedRouteObserver coercivelyImposedPunitiveState = samePunitiveRoute
imposedRouteObserver procedurallyReviewedPunitiveState = samePunitiveRoute

legitimacyObserver : LegitimacyState → LegitimacyCode
legitimacyObserver coercivelyImposedPunitiveState = coerciveLowLegitimacyCode
legitimacyObserver procedurallyReviewedPunitiveState = reviewedContestableCode

legitimacyDiffers :
  legitimacyObserver coercivelyImposedPunitiveState
  ≡ legitimacyObserver procedurallyReviewedPunitiveState → ⊥
legitimacyDiffers ()

------------------------------------------------------------------------
-- Route success and legitimacy are distinct.
------------------------------------------------------------------------

data SuccessfulImpositionPromotesLegitimacy : Set where

data ClinicalEvidencePromotesDemocraticMandate : Set where

data DemocraticMandatePromotesClinicalTruth : Set where

data AffectedVoicePromotesAutomaticPolicyAuthority : Set where

data StateRecognitionPromotesSovereignAuthority : Set where

successfulImpositionDoesNotPromoteLegitimacy :
  SuccessfulImpositionPromotesLegitimacy → ⊥
successfulImpositionDoesNotPromoteLegitimacy ()

clinicalEvidenceDoesNotPromoteDemocraticMandate :
  ClinicalEvidencePromotesDemocraticMandate → ⊥
clinicalEvidenceDoesNotPromoteDemocraticMandate ()

democraticMandateDoesNotPromoteClinicalTruth :
  DemocraticMandatePromotesClinicalTruth → ⊥
democraticMandateDoesNotPromoteClinicalTruth ()

affectedVoiceDoesNotPromoteAutomaticPolicyAuthority :
  AffectedVoicePromotesAutomaticPolicyAuthority → ⊥
affectedVoiceDoesNotPromoteAutomaticPolicyAuthority ()

stateRecognitionDoesNotPromoteSovereignAuthority :
  StateRecognitionPromotesSovereignAuthority → ⊥
stateRecognitionDoesNotPromoteSovereignAuthority ()

------------------------------------------------------------------------
-- Backward legitimacy demands for different classification routes.
------------------------------------------------------------------------

data LegitimacyDemand : Classify.GovernanceCone → LegitimacyAxis → Set where
  punitiveNeedsEmpiricalAdequacy :
    LegitimacyDemand Classify.punitiveSecurityCone empiricalAdequacyAxis
  punitiveNeedsAffectedVoice :
    LegitimacyDemand Classify.punitiveSecurityCone affectedSubjectVoiceAxis
  punitiveNeedsCommunityVoice :
    LegitimacyDemand Classify.punitiveSecurityCone affectedCommunityVoiceAxis
  punitiveNeedsDemocraticMandate :
    LegitimacyDemand Classify.punitiveSecurityCone democraticMandateAxis
  punitiveNeedsContestability :
    LegitimacyDemand Classify.punitiveSecurityCone proceduralContestabilityAxis
  punitiveNeedsHistoricalRepair :
    LegitimacyDemand Classify.punitiveSecurityCone historicalRepairAxis

  careNeedsClinicalJustification :
    LegitimacyDemand Classify.careResearchCone clinicalJustificationAxis
  careNeedsAffectedVoice :
    LegitimacyDemand Classify.careResearchCone affectedSubjectVoiceAxis
  careNeedsContestability :
    LegitimacyDemand Classify.careResearchCone proceduralContestabilityAxis

  ceremonialNeedsSovereignty :
    LegitimacyDemand Classify.sovereignCeremonialCone indigenousSovereigntyAxis
  ceremonialNeedsCommunityVoice :
    LegitimacyDemand Classify.sovereignCeremonialCone affectedCommunityVoiceAxis

------------------------------------------------------------------------
-- Feminist bridge retained directly.
------------------------------------------------------------------------

feministDrugBoundary : FeministDrug.FeministDrugClassificationAuthorityBoundary
feministDrugBoundary = FeministDrug.canonicalFeministDrugClassificationAuthorityBoundary

record DrugClassificationLegitimacyBoundary : Set where
  constructor drugClassificationLegitimacyBoundary
  field
    sameImposedRouteCanHideDifferentLegitimacy : Bool
    sameImposedRouteCanHideDifferentLegitimacyIsTrue :
      sameImposedRouteCanHideDifferentLegitimacy ≡ true
    coerciveEffectivenessEqualsLegitimacy : Bool
    coerciveEffectivenessEqualsLegitimacyIsFalse :
      coerciveEffectivenessEqualsLegitimacy ≡ false
    clinicalAuthorityEqualsDemocraticAuthority : Bool
    clinicalAuthorityEqualsDemocraticAuthorityIsFalse :
      clinicalAuthorityEqualsDemocraticAuthority ≡ false
    affectedVoiceIsIndependentLegitimacyCoordinate : Bool
    affectedVoiceIsIndependentLegitimacyCoordinateIsTrue :
      affectedVoiceIsIndependentLegitimacyCoordinate ≡ true
    sovereignAuthorityIsIndependentLegitimacyCoordinate : Bool
    sovereignAuthorityIsIndependentLegitimacyCoordinateIsTrue :
      sovereignAuthorityIsIndependentLegitimacyCoordinate ≡ true
    classifierVersionDeterminesLegitimacyByItself : Bool
    classifierVersionDeterminesLegitimacyByItselfIsFalse :
      classifierVersionDeterminesLegitimacyByItself ≡ false

canonicalDrugClassificationLegitimacyBoundary :
  DrugClassificationLegitimacyBoundary
canonicalDrugClassificationLegitimacyBoundary =
  drugClassificationLegitimacyBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
