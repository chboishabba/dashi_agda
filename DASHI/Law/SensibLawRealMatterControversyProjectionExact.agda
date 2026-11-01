module DASHI.Law.SensibLawRealMatterControversyProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- REAL-MATTER-CONTROVERSY-1 runtime parity.
--
-- One persisted Matter carries proposition fibres, reviewed evidence, typed
-- responses, controversy residuals, proof obligations and provenance. Client,
-- solicitor/counsel and court surfaces are projections of that same object.
-- They structure/reopen controversy; they do not adjudicate it.
------------------------------------------------------------------------

record PersistedControversyCoordinate : Set where
  constructor persisted-controversy-coordinate
  field
    matterRef : String
    controversyRef : String
    sourceReviewRef : String
    responseMode : Lee.ResponseMode
    disagreementKind : Lee.DisagreementKind
    residualRef : String
    obligationRef : String
    reverseSearchRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false
open PersistedControversyCoordinate public

record SharedMatterPersonaProjection : Set where
  constructor shared-matter-persona-projection
  field
    controversy : PersistedControversyCoordinate
    clientMatterRef : String
    solicitorMatterRef : String
    courtMatterRef : String
    clientSameMatter : clientMatterRef ≡ matterRef controversy
    solicitorSameMatter : solicitorMatterRef ≡ matterRef controversy
    courtSameMatter : courtMatterRef ≡ matterRef controversy
    typedResponsePreserved : Bool
    typedResponsePreservedIsTrue : typedResponsePreserved ≡ true
    reviewedAndCandidateStatesVisible : Bool
    reviewedAndCandidateStatesVisibleIsTrue : reviewedAndCandidateStatesVisible ≡ true
    normativeOrderRefsVisible : Bool
    normativeOrderRefsVisibleIsTrue : normativeOrderRefsVisible ≡ true
    commonGroundDoesNotPromoteTruth : Bool
    commonGroundDoesNotPromoteTruthIsTrue : commonGroundDoesNotPromoteTruth ≡ true
    reverseSearchUsesOpenObligations : Bool
    reverseSearchUsesOpenObligationsIsTrue : reverseSearchUsesOpenObligations ≡ true
    reverseSearchTargetsResidualDiscriminator : Bool
    reverseSearchTargetsResidualDiscriminatorIsTrue :
      reverseSearchTargetsResidualDiscriminator ≡ true
    determinesCredibility : Bool
    determinesCredibilityIsFalse : determinesCredibility ≡ false
    determinesUltimateFact : Bool
    determinesUltimateFactIsFalse : determinesUltimateFact ≡ false
    assignsNormativeWeight : Bool
    assignsNormativeWeightIsFalse : assignsNormativeWeight ≡ false
    entersFinalJudgment : Bool
    entersFinalJudgmentIsFalse : entersFinalJudgment ≡ false
open SharedMatterPersonaProjection public

canonicalControversy : PersistedControversyCoordinate
canonicalControversy =
  persisted-controversy-coordinate
    "matter:real"
    "controversy:real"
    "reviewed-evidence:real"
    Lee.admitOccurrenceDisputeCharacterisation
    Lee.characterisationDisagreement
    "residual:real"
    "obligation:real"
    "reverse-search:real"
    true refl
    false refl
    false refl
    false refl
    false refl

canonicalPersonaProjection : SharedMatterPersonaProjection
canonicalPersonaProjection =
  shared-matter-persona-projection
    canonicalControversy
    "matter:real"
    "matter:real"
    "matter:real"
    refl refl refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Two-order visibility.  Product projection may expose both legal-order kinds
-- and an explicit relationship; it may not collapse recognition into creation
-- or infer cross-order priority merely from display/persistence.
------------------------------------------------------------------------

record TwoOrderProjectionBoundary : Set where
  constructor two-order-projection-boundary
  field
    crownOrderKind : TwoOrder.LegalOrderKind
    indigenousOrderKind : TwoOrder.LegalOrderKind
    crownOrderPreserved : crownOrderKind ≡ TwoOrder.crownMunicipalLegalOrder
    indigenousOrderPreserved :
      indigenousOrderKind ≡ TwoOrder.indigenousNormativeLegalOrder
    crossOrderRecognitionCreatesIndigenousOrder : Bool
    crossOrderRecognitionCreatesIndigenousOrderIsFalse :
      crossOrderRecognitionCreatesIndigenousOrder ≡ false
    displayedNormativeOrderImpliesPriority : Bool
    displayedNormativeOrderImpliesPriorityIsFalse :
      displayedNormativeOrderImpliesPriority ≡ false
open TwoOrderProjectionBoundary public

canonicalTwoOrderProjectionBoundary : TwoOrderProjectionBoundary
canonicalTwoOrderProjectionBoundary =
  two-order-projection-boundary
    TwoOrder.crownMunicipalLegalOrder
    TwoOrder.indigenousNormativeLegalOrder
    refl refl
    false refl
    false refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data TypedResponseEqualsBooleanNegation : Set where
data AdmissionEqualsClaimTruth : Set where
data RecognitionEqualsCreation : Set where
data PersonaProjectionCreatesDifferentMatter : Set where
data ReverseSearchEqualsFinalJudgment : Set where
data MachineSynthesisEqualsCredibilityDetermination : Set where

typedResponseDoesNotEqualBooleanNegation : TypedResponseEqualsBooleanNegation → ⊥
typedResponseDoesNotEqualBooleanNegation ()

admissionDoesNotEqualClaimTruth : AdmissionEqualsClaimTruth → ⊥
admissionDoesNotEqualClaimTruth ()

recognitionDoesNotEqualCreation : RecognitionEqualsCreation → ⊥
recognitionDoesNotEqualCreation ()

personaProjectionDoesNotCreateDifferentMatter : PersonaProjectionCreatesDifferentMatter → ⊥
personaProjectionDoesNotCreateDifferentMatter ()

reverseSearchDoesNotEqualFinalJudgment : ReverseSearchEqualsFinalJudgment → ⊥
reverseSearchDoesNotEqualFinalJudgment ()

machineSynthesisDoesNotEqualCredibilityDetermination :
  MachineSynthesisEqualsCredibilityDetermination → ⊥
machineSynthesisDoesNotEqualCredibilityDetermination ()
