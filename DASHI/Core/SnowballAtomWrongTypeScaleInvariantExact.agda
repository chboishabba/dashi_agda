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

aScaleRelativeAtomNeedNotStayAtomic : AtomAtOneScaleIsAtomAtEveryScale → ⊥
aScaleRelativeAtomNeedNotStayAtomic ()

wrongTypeRemainsSystemIndexed : WrongTypeAtOneSystemIsWrongTypeAtEverySystem → ⊥
wrongTypeRemainsSystemIndexed ()

sourceAtomDoesNotCreateClassification : SourcePropositionAtomCreatesDownstreamClassification → ⊥
sourceAtomDoesNotCreateClassification ()
