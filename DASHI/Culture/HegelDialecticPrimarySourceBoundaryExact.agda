module DASHI.Culture.HegelDialecticPrimarySourceBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- HEGEL DIALECTIC PRIMARY-SOURCE BOUNDARY
--
-- Passage-level receipts for a bounded part of Hegel's dialectic.  The
-- thesis-antithesis-synthesis mnemonic is not treated as Hegel's literal
-- canonical formula, and the selected passages do not exhaust his system.
------------------------------------------------------------------------

hegelScienceOfLogicSource : Source.AttributedSource
hegelScienceOfLogicSource =
  Source.mkNoDOISource
    "G. W. F. Hegel"
    "Science of Logic"
    "original German publication 1812-1816; online English transcription used for passage recovery"
    "1812-1816"
    "https://www.marxists.org/reference/archive/hegel/works/hl/hl431.htm"
    Source.academicBookSource
    "primary philosophical source carrier for selected contradiction/self-movement propositions; access transcription does not transfer authorship"
    Source.publicAttribution

data SourceLayer : Set where
  primaryHegelProposition accessTranscription secondaryInterpretation dashiComparison : SourceLayer

record HegelDialecticReceipt : Set where
  constructor hegel-dialectic-receipt
  field
    source : Source.AttributedSource
    sourceLocation : String
    boundedProposition : String
    layer : SourceLayer
    exactPassageRecovered : Bool
    exhaustiveOfHegel : Bool
    importsDASHITheorem : Bool
open HegelDialecticReceipt public

contradictionTransitionReceipt : HegelDialecticReceipt
contradictionTransitionReceipt = hegel-dialectic-receipt
  hegelScienceOfLogicSource
  "Science of Logic, Doctrine of Essence, Contradiction, around §955"
  "Identity, difference and opposition are treated as passing into contradiction; contradiction is not represented as an accidental external error."
  primaryHegelProposition true false false

movementVitalityReceipt : HegelDialecticReceipt
movementVitalityReceipt = hegel-dialectic-receipt
  hegelScienceOfLogicSource
  "Science of Logic, Doctrine of Essence, Contradiction, §956-§958"
  "Contradiction is characterized as the root/principle of movement and self-movement rather than merely a subjective defect in thought."
  primaryHegelProposition true false false

livingUnityReceipt : HegelDialecticReceipt
livingUnityReceipt = hegel-dialectic-receipt
  hegelScienceOfLogicSource
  "Science of Logic, Doctrine of Essence, Contradiction, §959"
  "A living unity is described as containing and enduring contradiction; speculative thinking holds contradiction rather than simply resolving it into nothing."
  primaryHegelProposition true false false

reasonContradictionReceipt : HegelDialecticReceipt
reasonContradictionReceipt = hegel-dialectic-receipt
  (Source.mkNoDOISource
    "G. W. F. Hegel"
    "Science of Logic - Introduction"
    "original German publication 1812-1816; online English transcription used for passage recovery"
    "1812-1816"
    "https://www.marxists.org/reference/archive/hegel/works/hl/hlintro.htm"
    Source.academicBookSource
    "primary philosophical source carrier for bounded statements on understanding, contradiction and reason"
    Source.publicAttribution)
  "Science of Logic, Introduction, around §44"
  "Contradiction in finite determinations is presented as part of reason rising above limitations of understanding, not a license for arbitrary inconsistency."
  primaryHegelProposition true false false

data HegelDialecticMoment : Set where
  identityMoment differenceMoment oppositionMoment contradictionMoment transitionMoment selfMovementMoment : HegelDialecticMoment

data HegelDialecticRelation : HegelDialecticMoment → HegelDialecticMoment → Set where
  identityToDifference : HegelDialecticRelation identityMoment differenceMoment
  differenceToOpposition : HegelDialecticRelation differenceMoment oppositionMoment
  oppositionToContradiction : HegelDialecticRelation oppositionMoment contradictionMoment
  contradictionToTransition : HegelDialecticRelation contradictionMoment transitionMoment
  transitionToSelfMovement : HegelDialecticRelation transitionMoment selfMovementMoment

-- This graph is DASHI's comparison abstraction, not a literal diagram by Hegel.
data DASHISixNodeGraphIsLiteralHegelDiagram : Set where

dashISixNodeGraphIsNotLiteralHegelDiagram : DASHISixNodeGraphIsLiteralHegelDiagram → ⊥
dashISixNodeGraphIsNotLiteralHegelDiagram ()

data HegelDialecticIsThesisAntithesisSynthesisRecipe : Set where
data HegelContradictionMeansLogicalExplosion : Set where
data HegelContradictionMeansIrrationalism : Set where
data HegelSourceProvesDASHIFormalism : Set where
data DASHIRemainderIsIdenticalToHegelDoctrine : Set where
data PhilosophyTubeReadingIsHegelPrimaryText : Set where
data SelectedPassagesExhaustHegel : Set where

hegelDialecticIsNotEstablishedAsThreeWordRecipe : HegelDialecticIsThesisAntithesisSynthesisRecipe → ⊥
hegelDialecticIsNotEstablishedAsThreeWordRecipe ()
hegelContradictionDoesNotMeanExplosion : HegelContradictionMeansLogicalExplosion → ⊥
hegelContradictionDoesNotMeanExplosion ()
hegelContradictionDoesNotMeanIrrationalism : HegelContradictionMeansIrrationalism → ⊥
hegelContradictionDoesNotMeanIrrationalism ()
hegelSourceDoesNotProveDASHI : HegelSourceProvesDASHIFormalism → ⊥
hegelSourceDoesNotProveDASHI ()
dashIRemainderNotIdentifiedWithHegelDoctrine : DASHIRemainderIsIdenticalToHegelDoctrine → ⊥
dashIRemainderNotIdentifiedWithHegelDoctrine ()
philosophyTubeReadingDoesNotBecomePrimaryHegel : PhilosophyTubeReadingIsHegelPrimaryText → ⊥
philosophyTubeReadingDoesNotBecomePrimaryHegel ()
selectedPassagesDoNotExhaustHegel : SelectedPassagesExhaustHegel → ⊥
selectedPassagesDoNotExhaustHegel ()

record HegelDialecticPrimarySourceBoundary : Set where
  constructor hegel-dialectic-primary-source-boundary
  field
    contradictionTransitionRecovered : Bool
    contradictionSelfMovementRecovered : Bool
    livingUnityContradictionRecovered : Bool
    reasonBeyondFiniteUnderstandingRecovered : Bool
    thesisAntithesisSynthesisOwnedAsLiteralFormula : Bool
    irrationalismEstablished : Bool
    selectedPassagesExhaustSystem : Bool
    dashiIdentityEstablished : Bool
    strongerComparisonRequiresIndependentReceipt : Bool

canonicalHegelDialecticPrimarySourceBoundary : HegelDialecticPrimarySourceBoundary
canonicalHegelDialecticPrimarySourceBoundary =
  hegel-dialectic-primary-source-boundary true true true true false false false false true
