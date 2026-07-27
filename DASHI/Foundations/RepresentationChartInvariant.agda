module DASHI.Foundations.RepresentationChartInvariant where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A value is distinct from the chart in which it is displayed.
------------------------------------------------------------------------

record RatioRepresentation : Set where
  constructor ratio
  field
    numerator   : Nat
    denominator : Nat

open RatioRepresentation public

RatioEquivalent : RatioRepresentation → RatioRepresentation → Set
RatioEquivalent x y =
  numerator x * denominator y ≡ numerator y * denominator x

threeSix : RatioRepresentation
threeSix = ratio 3 6

oneHalf : RatioRepresentation
oneHalf = ratio 1 2

fiveTenths : RatioRepresentation
fiveTenths = ratio 5 10

fiftyHundredths : RatioRepresentation
fiftyHundredths = ratio 50 100

binaryPointOne : RatioRepresentation
binaryPointOne = ratio 1 2

threeSixIsOneHalf : RatioEquivalent threeSix oneHalf
threeSixIsOneHalf = refl

fiveTenthsIsOneHalf : RatioEquivalent fiveTenths oneHalf
fiveTenthsIsOneHalf = refl

fiftyHundredthsIsOneHalf : RatioEquivalent fiftyHundredths oneHalf
fiftyHundredthsIsOneHalf = refl

binaryPointOneIsOneHalf : RatioEquivalent binaryPointOne oneHalf
binaryPointOneIsOneHalf = refl

------------------------------------------------------------------------
-- Presentation charts for the same invariant rational point.
------------------------------------------------------------------------

data PresentationChart : Set where
  unreducedFractionChart : PresentationChart
  reducedFractionChart   : PresentationChart
  decimalChart           : PresentationChart
  percentageChart        : PresentationChart
  binaryRadixChart       : PresentationChart
  harmonicRatioChart     : PresentationChart
  stageInterpretationChart : PresentationChart
  situatedExplanationChart : PresentationChart

data HalfPresentation : Set where
  displayedThreeSix       : HalfPresentation
  displayedOneHalf        : HalfPresentation
  displayedDecimalPointFive : HalfPresentation
  displayedFiftyPercent   : HalfPresentation
  displayedBinaryPointOne : HalfPresentation

presentationChart : HalfPresentation → PresentationChart
presentationChart displayedThreeSix = unreducedFractionChart
presentationChart displayedOneHalf = reducedFractionChart
presentationChart displayedDecimalPointFive = decimalChart
presentationChart displayedFiftyPercent = percentageChart
presentationChart displayedBinaryPointOne = binaryRadixChart

presentationRatio : HalfPresentation → RatioRepresentation
presentationRatio displayedThreeSix = threeSix
presentationRatio displayedOneHalf = oneHalf
presentationRatio displayedDecimalPointFive = fiveTenths
presentationRatio displayedFiftyPercent = fiftyHundredths
presentationRatio displayedBinaryPointOne = binaryPointOne

presentationPreservesHalf :
  (p : HalfPresentation) →
  RatioEquivalent (presentationRatio p) oneHalf
presentationPreservesHalf displayedThreeSix = refl
presentationPreservesHalf displayedOneHalf = refl
presentationPreservesHalf displayedDecimalPointFive = refl
presentationPreservesHalf displayedFiftyPercent = refl
presentationPreservesHalf displayedBinaryPointOne = refl

record PresentationFibre (invariant : RatioRepresentation) : Set where
  constructor presentation-fibre
  field
    representation : RatioRepresentation
    chart          : PresentationChart
    evaluatesToInvariant : RatioEquivalent representation invariant

open PresentationFibre public

canonicalHalfPresentationFibre :
  HalfPresentation → PresentationFibre oneHalf
canonicalHalfPresentationFibre p =
  presentation-fibre
    (presentationRatio p)
    (presentationChart p)
    (presentationPreservesHalf p)

------------------------------------------------------------------------
-- The metacognitive lift makes the active frame explicit.
------------------------------------------------------------------------

FrameLift : Set → Set
FrameLift X = X × PresentationChart

frameLift : {X : Set} → X → PresentationChart → FrameLift X
frameLift x frame = x , frame

frameLiftValue : {X : Set} → (x : X) → (frame : PresentationChart) →
  proj₁ (frameLift x frame) ≡ x
frameLiftValue x frame = refl

frameLiftFrame : {X : Set} → (x : X) → (frame : PresentationChart) →
  proj₂ (frameLift x frame) ≡ frame
frameLiftFrame x frame = refl

------------------------------------------------------------------------
-- A chart atlas packages evaluation and lawful chart transition.
------------------------------------------------------------------------

record FramedAtlas (Value Representation Chart : Set) : Set₁ where
  field
    evaluate : Chart → Representation → Value
    transition : Chart → Chart → Representation → Representation
    transitionPreservesEvaluation :
      ∀ source target representation →
      evaluate target (transition source target representation)
      ≡ evaluate source representation
    transitionIdentity :
      ∀ chart representation →
      transition chart chart representation ≡ representation
    transitionComposition :
      ∀ first second third representation →
      transition second third (transition first second representation)
      ≡ transition first third representation

------------------------------------------------------------------------
-- Harmonic and partition readings are typed roles, not meanings of glyphs.
------------------------------------------------------------------------

data RatioRole : Set where
  normalizedOccupancyRole : RatioRole
  octaveFrequencyRole     : RatioRole
  midpointRole            : RatioRole
  percentageRole          : RatioRole
  scaleRefinementRole     : RatioRole
  harmonicReciprocalRole  : RatioRole

record TypedRatioReading : Set where
  constructor typed-ratio-reading
  field
    displayedRatio : RatioRepresentation
    invariantRatio : RatioRepresentation
    role           : RatioRole
    invariantProof : RatioEquivalent displayedRatio invariantRatio

threeSixOccupancyReading : TypedRatioReading
threeSixOccupancyReading =
  typed-ratio-reading threeSix oneHalf normalizedOccupancyRole refl

threeSixOctaveReading : TypedRatioReading
threeSixOctaveReading =
  typed-ratio-reading threeSix oneHalf octaveFrequencyRole refl

fiftyPercentReading : TypedRatioReading
fiftyPercentReading =
  typed-ratio-reading fiftyHundredths oneHalf percentageRole refl

harmonicTerm : Nat → RatioRepresentation
harmonicTerm n = ratio 1 (suc n)

firstHarmonicTerm : harmonicTerm 0 ≡ ratio 1 1
firstHarmonicTerm = refl

secondHarmonicTerm : harmonicTerm 1 ≡ oneHalf
secondHarmonicTerm = refl

threeSixIsSecondHarmonic : RatioEquivalent threeSix (harmonicTerm 1)
threeSixIsSecondHarmonic = refl

threeSixHarmonicReading : TypedRatioReading
threeSixHarmonicReading =
  typed-ratio-reading threeSix (harmonicTerm 1) harmonicReciprocalRole refl

refineRatio : Nat → RatioRepresentation → RatioRepresentation
refineRatio k r = ratio (k * numerator r) (k * denominator r)

refineRatioPreserves :
  (k : Nat) → (r : RatioRepresentation) →
  RatioEquivalent (refineRatio k r) r
refineRatioPreserves k r =
  trans
    (*-assoc k (numerator r) (denominator r))
    (trans
      (cong (k *_) (*-comm (numerator r) (denominator r)))
      (trans
        (sym (*-assoc k (denominator r) (numerator r)))
        (*-comm (k * denominator r) (numerator r))))

threefoldHalfRefinement : refineRatio 3 oneHalf ≡ threeSix
threefoldHalfRefinement = refl

threefoldHalfRefinementPreserves :
  RatioEquivalent (refineRatio 3 oneHalf) oneHalf
threefoldHalfRefinementPreserves = refineRatioPreserves 3 oneHalf

------------------------------------------------------------------------
-- 3/6/9 supports several different typed operations.  No operation below
-- identifies those roles definitionally.
------------------------------------------------------------------------

data ThreeSixNineUse : Set where
  doublingUse       : ThreeSixNineUse
  normalizedRatioUse : ThreeSixNineUse
  axisTimesFibreUse : ThreeSixNineUse
  matrixSheetUse    : ThreeSixNineUse
  residueObservationUse : ThreeSixNineUse
  semanticStageUse  : ThreeSixNineUse
  harmonicRatioUse  : ThreeSixNineUse

record ContextualThreeSixNineObservation (System : Set) : Set₁ where
  field
    Signature : Set
    Context   : Set
    observationMap : System → Signature
    interpretationContext : Context
    selectedUse : ThreeSixNineUse

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record RepresentationAuthorityBoundary : Set where
  field
    glyphIsInvariantValueClaimed : Bool
    oneChartIsGloballyPrivilegedClaimed : Bool
    frameCanBeInspected : Bool
    frameCanBeCompared : Bool
    presentationFibreIsGroupCoverClaimed : Bool
    harmonicRoleIsContextDependent : Bool

canonicalRepresentationAuthorityBoundary : RepresentationAuthorityBoundary
canonicalRepresentationAuthorityBoundary = record
  { glyphIsInvariantValueClaimed = false
  ; oneChartIsGloballyPrivilegedClaimed = false
  ; frameCanBeInspected = true
  ; frameCanBeCompared = true
  ; presentationFibreIsGroupCoverClaimed = false
  ; harmonicRoleIsContextDependent = true
  }

representationSummary : String
representationSummary =
  "A value is carried together with its chart, scale and relation; 3/6, 1/2, 0.5, 0.1 base 2 and 50% are distinct presentations of one rational point."
