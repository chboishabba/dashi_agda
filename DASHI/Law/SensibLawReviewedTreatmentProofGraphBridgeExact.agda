module DASHI.Law.SensibLawReviewedTreatmentProofGraphBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact as Search

------------------------------------------------------------------------
-- S20.10 REVIEWED TREATMENT -> PROOF GRAPH
--
-- This is a generic role bridge, not a matter-specific reducer.  A reviewed
-- party treatment can become a candidate graph atom/edge, but the bridge does
-- not upgrade a submission to a holding, a citation to a proposition, or a
-- counter-defeater to current law.
------------------------------------------------------------------------

data TreatmentClass : Set where
  supportTreatment : TreatmentClass
  defeaterTreatment : TreatmentClass
  counterDefeaterTreatment : TreatmentClass
  authorityScopeTreatment : TreatmentClass

data AtomClass : Set where
  authorityAtom : AtomClass
  defeaterAtom : AtomClass
  counterDefeaterAtom : AtomClass

atomClass : TreatmentClass → AtomClass
atomClass supportTreatment = authorityAtom
atomClass defeaterTreatment = defeaterAtom
atomClass counterDefeaterTreatment = counterDefeaterAtom
atomClass authorityScopeTreatment = defeaterAtom

searchRole : TreatmentClass → Search.AdversarialRole
searchRole supportTreatment = Search.supportSearch
searchRole defeaterTreatment = Search.defeaterSearch
searchRole counterDefeaterTreatment = Search.counterDefeaterSearch
searchRole authorityScopeTreatment = Search.counterDefeaterSearch

supportCompilesToSupport :
  searchRole supportTreatment ≡ Search.supportSearch
supportCompilesToSupport = refl

defeaterCompilesToDefeater :
  searchRole defeaterTreatment ≡ Search.defeaterSearch
defeaterCompilesToDefeater = refl

counterDefeaterCompilesToCounterSearch :
  searchRole counterDefeaterTreatment ≡ Search.counterDefeaterSearch
counterDefeaterCompilesToCounterSearch = refl

authorityScopeRemainsAdversarial :
  searchRole authorityScopeTreatment ≡ Search.counterDefeaterSearch
authorityScopeRemainsAdversarial = refl

------------------------------------------------------------------------
-- Exact-target discipline.
------------------------------------------------------------------------

data TargetCardinality : Set where
  zeroTargets : TargetCardinality
  oneTarget : TargetCardinality
  manyTargets : TargetCardinality

data CounterApplication : Set where
  noApplication : CounterApplication
  exactApplication : CounterApplication

applyCounter : TargetCardinality → CounterApplication
applyCounter zeroTargets = noApplication
applyCounter oneTarget = exactApplication
applyCounter manyTargets = noApplication

ambiguousCounterDoesNotGuess :
  applyCounter manyTargets ≡ noApplication
ambiguousCounterDoesNotGuess = refl

exactSingleCounterMayApply :
  applyCounter oneTarget ≡ exactApplication
exactSingleCounterMayApply = refl

------------------------------------------------------------------------
-- Authority boundaries.
------------------------------------------------------------------------

data PartySubmissionIsHolding : Set where
data CitationIsReviewedProposition : Set where
data CounterDefeaterIsCurrentLaw : Set where
data TreatmentCreatesClaimTruth : Set where

submissionDoesNotBecomeHolding :
  PartySubmissionIsHolding → ⊥
submissionDoesNotBecomeHolding ()

citationDoesNotBecomeProposition :
  CitationIsReviewedProposition → ⊥
citationDoesNotBecomeProposition ()

counterDefeaterDoesNotBecomeCurrentLaw :
  CounterDefeaterIsCurrentLaw → ⊥
counterDefeaterDoesNotBecomeCurrentLaw ()

treatmentDoesNotCreateClaimTruth :
  TreatmentCreatesClaimTruth → ⊥
treatmentDoesNotCreateClaimTruth ()

record ReviewedTreatmentBridgeBoundary : Set where
  constructor reviewedTreatmentBridgeBoundary
  field
    bridgeIsMatterGeneric : Bool
    bridgeIsMatterGenericIsTrue : bridgeIsMatterGeneric ≡ true

    exactSingleTargetRequiredForAutomaticCounterApplication : Bool
    exactSingleTargetRequiredForAutomaticCounterApplicationIsTrue :
      exactSingleTargetRequiredForAutomaticCounterApplication ≡ true

    ambiguousCounterTargetMayBeGuessed : Bool
    ambiguousCounterTargetMayBeGuessedIsFalse :
      ambiguousCounterTargetMayBeGuessed ≡ false

    reviewedSubmissionCreatesHolding : Bool
    reviewedSubmissionCreatesHoldingIsFalse :
      reviewedSubmissionCreatesHolding ≡ false

    reviewedTreatmentCreatesClaimTruth : Bool
    reviewedTreatmentCreatesClaimTruthIsFalse :
      reviewedTreatmentCreatesClaimTruth ≡ false

open ReviewedTreatmentBridgeBoundary public

canonicalReviewedTreatmentBridgeBoundary : ReviewedTreatmentBridgeBoundary
canonicalReviewedTreatmentBridgeBoundary =
  reviewedTreatmentBridgeBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
