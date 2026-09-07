module DASHI.Law.SensibLawWaterproofArgumentGapSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result

------------------------------------------------------------------------
-- WATERPROOF-ARGUMENT GAP SEARCH
--
-- A nearly complete argument exposes the smallest typed missing proposition.
-- Search is asked for an admissible inhabitant of that node, not for documents
-- vaguely similar to the conclusion.
------------------------------------------------------------------------

data ArgumentNodeStatus : Set where
  premisePaid : ArgumentNodeStatus
  premiseContested : ArgumentNodeStatus
  premiseMissing : ArgumentNodeStatus
  premiseInapplicable : ArgumentNodeStatus
  premiseAuthorityBlocked : ArgumentNodeStatus
  conclusionCandidate : ArgumentNodeStatus
  conclusionAdmitted : ArgumentNodeStatus


record ArgumentNode : Set where
  constructor argumentNode
  field
    nodeReference : String
    propositionReference : String
    status : ArgumentNodeStatus
    authorityRequirementReference : String
    evidenceRequirementReference : String
    consumerReference : String

open ArgumentNode public

record ArgumentEdge : Set where
  constructor argumentEdge
  field
    fromNodeReference : String
    toNodeReference : String
    relationReference : String
    inferenceAuthorityReference : String
    edgeReference : String

open ArgumentEdge public

record ArgumentProofGraph : Set₁ where
  constructor argumentProofGraph
  field
    consumerReference : String
    nodes : List ArgumentNode
    edges : List ArgumentEdge
    targetConclusionReference : String
    graphReference : String

open ArgumentProofGraph public

record MinimalArgumentGap : Set₁ where
  constructor minimalArgumentGap
  field
    graph : ArgumentProofGraph
    missingNode : ArgumentNode
    missingNodeIsRequiredReceipt : Set
    allEarlierRequiredNodesPaidReceipt : Set
    smallestLiveGapReceipt : Set
    gapReference : String

open MinimalArgumentGap public

record GapSearchCompilation : Set₁ where
  constructor gapSearchCompilation
  field
    gap : MinimalArgumentGap
    requiredProducer : Intent.ProducerClass
    searchIntent : Intent.SearchIntent
    sameTargetPropositionReceipt : Set
    compilationReference : String

open GapSearchCompilation public

record CandidateGapPayment : Set₁ where
  constructor candidateGapPayment
  field
    gap : MinimalArgumentGap
    searchAssessmentReference : String
    candidateAuthorityReference : String
    candidatePropositionReference : String
    paymentAssessment : Result.ProofPaymentAssessment
    paymentReference : String

open CandidateGapPayment public

record WaterproofArgumentReceipt : Set₁ where
  constructor waterproofArgumentReceipt
  field
    graph : ArgumentProofGraph
    allRequiredPremisesPaidReceipt : Set
    allInferenceEdgesAuthorisedReceipt : Set
    noLiveDefeaterReceipt : Set
    jurisdictionReceipt : Set
    temporalReceipt : Set
    authorityReceipt : Set
    consumerClosureReceipt : Set
    receiptReference : String

open WaterproofArgumentReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OneFoundAuthorityAutomaticallyWaterproof : Set where
data AllPremisesTextuallyPresentAutomaticallyValid : Set where
data MissingNodeMayBeFilledByWrongProducer : Set where
data NoRetrievedDefeaterMeansNoDefeaterExists : Set where

data CandidateGapPaymentAutomaticallyClosesGraph : Set where

oneAuthorityDoesNotWaterproofArgument : OneFoundAuthorityAutomaticallyWaterproof → ⊥
oneAuthorityDoesNotWaterproofArgument ()

textualPresenceDoesNotValidatePremises : AllPremisesTextuallyPresentAutomaticallyValid → ⊥
textualPresenceDoesNotValidatePremises ()

wrongProducerCannotSilentlyFillGap : MissingNodeMayBeFilledByWrongProducer → ⊥
wrongProducerCannotSilentlyFillGap ()

noRetrievedDefeaterDoesNotProveNoDefeater : NoRetrievedDefeaterMeansNoDefeaterExists → ⊥
noRetrievedDefeaterDoesNotProveNoDefeater ()

candidatePaymentDoesNotAutoCloseGraph : CandidateGapPaymentAutomaticallyClosesGraph → ⊥
candidatePaymentDoesNotAutoCloseGraph ()

record WaterproofArgumentBoundary : Set where
  constructor waterproofArgumentBoundary
  field
    smallestGapMayDriveSearch : Bool
    smallestGapMayDriveSearchIsTrue : smallestGapMayDriveSearch ≡ true
    gapSearchIsProducerTyped : Bool
    gapSearchIsProducerTypedIsTrue : gapSearchIsProducerTyped ≡ true
    supportingAuthorityAloneMakesArgumentWaterproof : Bool
    supportingAuthorityAloneMakesArgumentWaterproofIsFalse :
      supportingAuthorityAloneMakesArgumentWaterproof ≡ false
    defeaterInspectionRemainsIndependent : Bool
    defeaterInspectionRemainsIndependentIsTrue : defeaterInspectionRemainsIndependent ≡ true

canonicalWaterproofArgumentBoundary : WaterproofArgumentBoundary
canonicalWaterproofArgumentBoundary =
  waterproofArgumentBoundary true refl true refl false refl true refl
