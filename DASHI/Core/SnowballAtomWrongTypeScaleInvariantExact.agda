module DASHI.Core.SnowballAtomWrongTypeScaleInvariantExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- ATOM / WRONGTYPE / SCALE INVARIANT
--
-- An Atom is consumer/query-relative: the smallest currently admitted grain
-- sufficient to be reasoned about as one proposition/unit at that layer.
-- It is not asserted to be ontologically indivisible and is not identified
-- with a programming-language atom.
------------------------------------------------------------------------

data SemanticScale : Set where
  sourceProposition legalNorm legalElement deviceProcess rtlLogic physicalLayout
  manufacturedObject economicObservation policyClassification : SemanticScale

record AtomGrain (Consumer Query : Set) : Set₁ where
  constructor atom-grain
  field
    Atom : Set
    consumer : Consumer
    query : Query
    scale : Atom → SemanticScale
    provenanceRequired : Atom → Bool
    furtherRefinementAllowed : Atom → Bool
open AtomGrain public

record WrongTypeFamily (Atom Classification : Set) : Set₁ where
  constructor wrong-type-family
  field
    classify : Atom → Classification
    classificationNeedsContext : Bool
    sameAtomMayHaveDifferentSystemInterpretations : Bool
    classificationCreatesTruth : Bool
open WrongTypeFamily public

------------------------------------------------------------------------
-- ACQUISITION / PAYMENT SNOWBALL INVARIANT
--
-- Evidence may be acquired opportunistically and retained out of dependency
-- order. Acquisition is append-only with respect to the retained carrier;
-- payment remains consumer/query-relative and receipt-gated. Thus later
-- evidence may already be present while the first unpaid dependency remains
-- authoritative. This abstracts the receipt-indexed scientific-wall pattern
-- without making any particular wall, scheduler, or domain universal.
------------------------------------------------------------------------

record SnowballAcquisitionPaymentInvariant (Atom Receipt : Set) : Set₁ where
  constructor snowball-acquisition-payment-invariant
  field
    acquired : Atom → Bool
    paid : Atom → Bool
    receiptAtom : Receipt → Atom
    receiptAdmitsPayment : (receipt : Receipt) → paid (receiptAtom receipt) ≡ true
    outOfOrderAcquisitionMayBeRetained : Bool
    acquisitionAutomaticallyCreatesPayment : Bool
    laterAcquisitionMaySkipFirstUnpaidDependency : Bool
    paymentRemainsConsumerRelative : Bool
    acquisitionHistoryMayGrowWithoutConclusionPromotion : Bool
open SnowballAcquisitionPaymentInvariant public

record SnowballAcquisitionPaymentBoundary : Set where
  constructor snowball-acquisition-payment-boundary
  field
    acquisitionOrderEqualsDependencyOrder : Bool
    retainedEvidenceEqualsPaidDependency : Bool
    observedAxisEqualsReceiptBearingPayment : Bool
    allObservedCoordinatesCreateTerminalConclusion : Bool
    firstUnpaidDependencyRemainsAuthoritative : Bool
    laterEvidenceMayRemainRetained : Bool
    paymentRequiresConsumerAdequacy : Bool
open SnowballAcquisitionPaymentBoundary public

canonicalSnowballAcquisitionPaymentBoundary : SnowballAcquisitionPaymentBoundary
canonicalSnowballAcquisitionPaymentBoundary =
  snowball-acquisition-payment-boundary false false false false true true true

record ScaleTransportBoundary : Set where
  constructor scale-transport-boundary
  field
    atomMeansProgrammingAtom : Bool
    atomMeansOntologicallyIndivisible : Bool
    atomMayRefineForNewConsumer : Bool
    wrongTypeMeansCompilerTypeError : Bool
    wrongTypeMayBeSystemPerspectiveIndexed : Bool
    sourceAtomEqualsLegalElementProof : Bool
    rtlCorrectnessEqualsFabricatedOutcome : Bool
    economicSourcePropositionEqualsPolicyClassification : Bool
open ScaleTransportBoundary public

canonicalScaleTransportBoundary : ScaleTransportBoundary
canonicalScaleTransportBoundary =
  scale-transport-boundary false false true false true false false false

data AtomAtOneScaleIsAtomAtEveryScale : Set where
data WrongTypeAtOneSystemIsWrongTypeAtEverySystem : Set where
data SourcePropositionAtomCreatesDownstreamClassification : Set where
data RetainedAcquisitionCreatesPayment : Set where
data LaterEvidenceSkipsFirstUnpaidDependency : Set where

aScaleRelativeAtomNeedNotStayAtomic : AtomAtOneScaleIsAtomAtEveryScale → ⊥
aScaleRelativeAtomNeedNotStayAtomic ()

wrongTypeRemainsSystemIndexed : WrongTypeAtOneSystemIsWrongTypeAtEverySystem → ⊥
wrongTypeRemainsSystemIndexed ()

sourceAtomDoesNotCreateClassification : SourcePropositionAtomCreatesDownstreamClassification → ⊥
sourceAtomDoesNotCreateClassification ()

retainedAcquisitionDoesNotCreatePayment : RetainedAcquisitionCreatesPayment → ⊥
retainedAcquisitionDoesNotCreatePayment ()

laterEvidenceDoesNotSkipFirstUnpaidDependency : LaterEvidenceSkipsFirstUnpaidDependency → ⊥
laterEvidenceDoesNotSkipFirstUnpaidDependency ()
