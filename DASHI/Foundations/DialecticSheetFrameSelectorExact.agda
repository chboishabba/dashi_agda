module DASHI.Foundations.DialecticSheetFrameSelectorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

------------------------------------------------------------------------
-- Three proposition slots, binary input values, ternary comparator results,
-- and a nine-cell relational sheet are separate arities.
------------------------------------------------------------------------

data Bit2 : Set where
  bit0 bit1 : Bit2

record BinaryDialecticAtom : Set where
  constructor binaryAtom
  field
    conditionOne conditionTwo synthesisSlot : Bit2

open BinaryDialecticAtom public

binaryComparator : Bit2 → Bit2 → BT.BalancedDigit
binaryComparator bit0 bit0 = BT.zeroDigit
binaryComparator bit0 bit1 = BT.neg
binaryComparator bit1 bit0 = BT.pos
binaryComparator bit1 bit1 = BT.zeroDigit

record TernaryCoordinateComparison : Set where
  constructor ternaryCoordinateComparison
  field
    firstResult secondResult thirdResult : BT.BalancedDigit

open TernaryCoordinateComparison public

compareCoordinates :
  BinaryDialecticAtom → BinaryDialecticAtom → TernaryCoordinateComparison
compareCoordinates x y =
  ternaryCoordinateComparison
    (binaryComparator (conditionOne x) (conditionOne y))
    (binaryComparator (conditionTwo x) (conditionTwo y))
    (binaryComparator (synthesisSlot x) (synthesisSlot y))

record ComparisonSheet3x3 : Set where
  constructor comparisonSheet3x3
  field
    c11 c12 c13
      c21 c22 c23
      c31 c32 c33 : BT.BalancedDigit

open ComparisonSheet3x3 public

sheetJoin : BinaryDialecticAtom → BinaryDialecticAtom → ComparisonSheet3x3
sheetJoin x y =
  comparisonSheet3x3
    (binaryComparator (conditionOne x) (conditionOne y))
    (binaryComparator (conditionOne x) (conditionTwo y))
    (binaryComparator (conditionOne x) (synthesisSlot y))
    (binaryComparator (conditionTwo x) (conditionOne y))
    (binaryComparator (conditionTwo x) (conditionTwo y))
    (binaryComparator (conditionTwo x) (synthesisSlot y))
    (binaryComparator (synthesisSlot x) (conditionOne y))
    (binaryComparator (synthesisSlot x) (conditionTwo y))
    (binaryComparator (synthesisSlot x) (synthesisSlot y))

allAffirmedBinary : BinaryDialecticAtom
allAffirmedBinary = binaryAtom bit1 bit1 bit1

firstDeniedOther : BinaryDialecticAtom
firstDeniedOther = binaryAtom bit0 bit1 bit1

coordinateComparatorRegression :
  compareCoordinates allAffirmedBinary firstDeniedOther
  ≡ ternaryCoordinateComparison BT.pos BT.zeroDigit BT.zeroDigit
coordinateComparatorRegression = refl

------------------------------------------------------------------------
-- A six-line observation retains lower and upper triads.  Its total amplitude
-- is secondary to the constituent patterns and to the location of open lines.
------------------------------------------------------------------------

record HexagramObservation : Set where
  constructor hexagramObservation
  field
    lowerTriad upperTriad : BT.TriadPattern
    lowerAmplitude upperAmplitude : Nat
    lowerBalanceExact :
      BT.patternBalance lowerTriad ≡ BT.signedBalance lowerAmplitude 0
    upperBalanceExact :
      BT.patternBalance upperTriad ≡ BT.signedBalance upperAmplitude 0

open HexagramObservation public

stageFiveHexagram : HexagramObservation
stageFiveHexagram =
  hexagramObservation BT.allPositive BT.twoPositiveOneOpen 3 2 refl refl

stageFiveHexagramTotal :
  lowerAmplitude stageFiveHexagram + upperAmplitude stageFiveHexagram ≡ 5
stageFiveHexagramTotal = refl

------------------------------------------------------------------------
-- An image first produces typed receipts.  A context projects receipts to a
-- hexagram; the projection is not itself a truth or prediction oracle.
------------------------------------------------------------------------

data ImageFeatureKind : Set where
  foregroundBackground : ImageFeatureKind
  directionFeature : ImageFeatureKind
  enclosureFeature : ImageFeatureKind
  repetitionFeature : ImageFeatureKind
  interruptionFeature : ImageFeatureKind
  scaleFeature : ImageFeatureKind
  movementFeature : ImageFeatureKind

record ImageFeatureReceipt : Set where
  constructor imageFeatureReceipt
  field
    kind : ImageFeatureKind
    reading : BT.BalancedDigit
    provenance : String

record ImageHexagramProjection : Set where
  constructor imageHexagramProjection
  field
    context : String
    receipts : List ImageFeatureReceipt
    observation : HexagramObservation
    externalPredictionClaimed : Bool
    externalPredictionClaimedIsFalse : externalPredictionClaimed ≡ false

canonicalImageProjection : ImageHexagramProjection
canonicalImageProjection =
  imageHexagramProjection
    "lower local coherence; upper unresolved synthesis"
    (imageFeatureReceipt enclosureFeature BT.pos "visible enclosure"
     ∷ imageFeatureReceipt repetitionFeature BT.pos "repeated motif"
     ∷ imageFeatureReceipt interruptionFeature BT.zeroDigit "open terminal feature"
     ∷ [])
    stageFiveHexagram
    false refl

------------------------------------------------------------------------
-- The selector returns a frame together with proofs that the two conditions
-- and their synthesis are affirmed and that the synthesis is actually a glue
-- of the first two.  Returning only Bool would erase the witness.
------------------------------------------------------------------------

record FrameSemantics (Frame Condition : Set) : Set₁ where
  field
    evaluate : Frame → Condition → BT.BalancedDigit
    synthesises : Frame → Condition → Condition → Condition → Set

open FrameSemantics public

record FrameWitness
  {Frame Condition : Set}
  (semantics : FrameSemantics Frame Condition)
  (P Q S : Condition) : Set where
  constructor frameWitness
  field
    frame : Frame
    firstAffirmed : evaluate semantics frame P ≡ BT.pos
    secondAffirmed : evaluate semantics frame Q ≡ BT.pos
    synthesisAffirmed : evaluate semantics frame S ≡ BT.pos
    synthesisIsGlue : synthesises semantics frame P Q S

open FrameWitness public

data Optional (A : Set) : Set where
  none : Optional A
  some : A → Optional A

data ExampleFrame : Set where
  inhabitableFrame counterFrame : ExampleFrame

data ExampleCondition : Set where
  firstCondition secondCondition joinedSynthesis : ExampleCondition

exampleEvaluate : ExampleFrame → ExampleCondition → BT.BalancedDigit
exampleEvaluate inhabitableFrame firstCondition = BT.pos
exampleEvaluate inhabitableFrame secondCondition = BT.pos
exampleEvaluate inhabitableFrame joinedSynthesis = BT.pos
exampleEvaluate counterFrame firstCondition = BT.pos
exampleEvaluate counterFrame secondCondition = BT.pos
exampleEvaluate counterFrame joinedSynthesis = BT.neg

data ExampleSynthesis :
  ExampleFrame → ExampleCondition → ExampleCondition → ExampleCondition → Set where
  inhabitableGlue :
    ExampleSynthesis inhabitableFrame firstCondition secondCondition joinedSynthesis

exampleSemantics : FrameSemantics ExampleFrame ExampleCondition
exampleSemantics = record
  { evaluate = exampleEvaluate
  ; synthesises = ExampleSynthesis
  }

inhabitableFrameWitness :
  FrameWitness exampleSemantics firstCondition secondCondition joinedSynthesis
inhabitableFrameWitness =
  frameWitness inhabitableFrame refl refl refl inhabitableGlue

selectInhabitableFrame :
  Optional
    (FrameWitness exampleSemantics
      firstCondition secondCondition joinedSynthesis)
selectInhabitableFrame = some inhabitableFrameWitness

------------------------------------------------------------------------
-- Tarot generates candidate frames downstream from the observation.  It does
-- not make a candidate frame universally valid or externally predictive.
------------------------------------------------------------------------

data FrameAuthority : Set where
  observedCarrierAuthority : FrameAuthority
  declaredSymbolicAuthority : FrameAuthority
  unsupportedAuthority : FrameAuthority

record TarotFrameCandidate : Set where
  constructor tarotFrameCandidate
  field
    cardName : String
    frameDescription : String
    authority : FrameAuthority
    locallyInhabitable : Bool
    universallyTrueClaimed : Bool
    universallyTrueClaimedIsFalse : universallyTrueClaimed ≡ false

empressStageThreeCandidate : TarotFrameCandidate
empressStageThreeCandidate =
  tarotFrameCandidate
    "The Empress"
    "a local frame in which condition, relation, and synthesis cohere"
    declaredSymbolicAuthority true false refl

record SelectorAuthorityBoundary : Set where
  constructor selectorAuthorityBoundary
  field
    localWitnessImpliesUniversalTruth : Bool
    localWitnessImpliesUniversalTruthIsFalse :
      localWitnessImpliesUniversalTruth ≡ false
    tarotCandidateCreatesExternalPrediction : Bool
    tarotCandidateCreatesExternalPredictionIsFalse :
      tarotCandidateCreatesExternalPrediction ≡ false

canonicalSelectorAuthorityBoundary : SelectorAuthorityBoundary
canonicalSelectorAuthorityBoundary =
  selectorAuthorityBoundary false refl false refl
