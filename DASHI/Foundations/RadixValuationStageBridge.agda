module DASHI.Foundations.RadixValuationStageBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec; []; _∷_)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.TrackedPrimes as TP

------------------------------------------------------------------------
-- The radix supplies place weights; the radix point supplies exponent zero.
------------------------------------------------------------------------

record RadixChart : Set where
  constructor radix-chart
  field
    radix : Nat
    scaleOrigin : Nat
    displayLabel : String

open RadixChart public

decimalChart : RadixChart
decimalChart = radix-chart 10 0 "base-10 display with the radix point at exponent zero"

binaryChart : RadixChart
binaryChart = radix-chart 2 0 "base-2 display with the radix point at exponent zero"

record PositionalReading : Set where
  field
    glyphSequence : List Nat
    chart : RadixChart
    evaluationLabel : String

------------------------------------------------------------------------
-- A decimal display and a p-adic valuation are independent coordinates.
------------------------------------------------------------------------

record DisplayValuationReading : Set where
  field
    displayBase : Nat
    valuationPrime : Nat
    radixOriginExplicit : Bool
    displayBaseEqualsValuationPrimeRequired : Bool
    readingLabel : String

canonicalDecimalPAdicReading : Nat → DisplayValuationReading
canonicalDecimalPAdicReading p = record
  { displayBase = 10
  ; valuationPrime = p
  ; radixOriginExplicit = true
  ; displayBaseEqualsValuationPrimeRequired = false
  ; readingLabel =
      "The glyphs may be displayed conventionally in decimal while closeness and refinement are read from the selected p-adic valuation origin."
  }

------------------------------------------------------------------------
-- Prefix agreement begins at the radix/valuation origin and moves outward.
------------------------------------------------------------------------

RadialAddress : Nat → Nat → Set
RadialAddress p depth = Vec (Fin p) depth

data RadixOriginPrefix {p : Nat} :
  ∀ {depth} → Nat → RadialAddress p depth → RadialAddress p depth → Set where
  radix-prefix-zero :
    ∀ {depth} {x y : RadialAddress p depth} →
    RadixOriginPrefix 0 x y

  radix-prefix-cons :
    ∀ {depth matched}
      {x y : Fin p}
      {xs ys : RadialAddress p depth} →
    x ≡ y →
    RadixOriginPrefix matched xs ys →
    RadixOriginPrefix (suc matched) (x ∷ xs) (y ∷ ys)

radixPrefixReflexive :
  ∀ {p depth} (address : RadialAddress p depth) →
  RadixOriginPrefix depth address address
radixPrefixReflexive [] = radix-prefix-zero
radixPrefixReflexive (x ∷ xs) =
  radix-prefix-cons refl (radixPrefixReflexive xs)

record PrefixUltrametricReading {p depth : Nat}
  (x y : RadialAddress p depth) : Set where
  field
    sharedFromOrigin : Nat
    prefixWitness : RadixOriginPrefix sharedFromOrigin x y
    firstDifferenceDeterminesScale : Bool

------------------------------------------------------------------------
-- Coarse graining truncates an outward extension; fine graining appends one.
------------------------------------------------------------------------

data RadialTreeAddress (p : Nat) : Nat → Set where
  radial-root : RadialTreeAddress p zero
  radial-extend :
    ∀ {depth} →
    RadialTreeAddress p depth →
    Fin p →
    RadialTreeAddress p (suc depth)

radialCoarsen :
  ∀ {p depth} →
  RadialTreeAddress p (suc depth) →
  RadialTreeAddress p depth
radialCoarsen (radial-extend parent digit) = parent

radialCoarsenAfterExtend :
  ∀ {p depth}
    (parent : RadialTreeAddress p depth)
    (digit : Fin p) →
  radialCoarsen (radial-extend parent digit) ≡ parent
radialCoarsenAfterExtend parent digit = refl

------------------------------------------------------------------------
-- Decimal 9 -> 10 -> 11 is one display of a radix-independent carry grammar.
------------------------------------------------------------------------

record CarryGrammar : Set where
  field
    base : Nat
    terminalLocalDigit : Nat
    carriedUnitValue : Nat
    carryPlusLocalUnitValue : Nat
    terminalPlusOneCarries : terminalLocalDigit + 1 ≡ carriedUnitValue
    carriedUnitPlusOneJoins : carriedUnitValue + 1 ≡ carryPlusLocalUnitValue
    carryGlyph : String
    joinedGlyph : String

canonicalDecimalCarryGrammar : CarryGrammar
canonicalDecimalCarryGrammar = record
  { base = 10
  ; terminalLocalDigit = 9
  ; carriedUnitValue = 10
  ; carryPlusLocalUnitValue = 11
  ; terminalPlusOneCarries = refl
  ; carriedUnitPlusOneJoins = refl
  ; carryGlyph = "10"
  ; joinedGlyph = "11"
  }

------------------------------------------------------------------------
-- Stage 1 and Stage 10 share a unit role across scale, not a numeric value.
-- Stage 11 carries the new-scale unit together with one local increment.
------------------------------------------------------------------------

data StageScaleRole : Set where
  originRole : StageScaleRole
  currentPlaceUnitRole : StageScaleRole
  carriedPlaceUnitRole : StageScaleRole
  carryPlusLocalUnitRole : StageScaleRole
  ordinaryStageRole : StageScaleRole

stageScaleRole : Atlas.StageAtlasZeroToEleven → StageScaleRole
stageScaleRole Atlas.atlas-0 = originRole
stageScaleRole Atlas.atlas-1 = currentPlaceUnitRole
stageScaleRole Atlas.atlas-10 = carriedPlaceUnitRole
stageScaleRole Atlas.atlas-11 = carryPlusLocalUnitRole
stageScaleRole _ = ordinaryStageRole

data SameUnitRoleAcrossScale :
  Atlas.StageAtlasZeroToEleven →
  Atlas.StageAtlasZeroToEleven →
  Set where
  stage1ToStage10UnitLift :
    SameUnitRoleAcrossScale Atlas.atlas-1 Atlas.atlas-10

record StageCarryJoin : Set where
  field
    localUnit : Atlas.StageAtlasZeroToEleven
    carriedUnit : Atlas.StageAtlasZeroToEleven
    joinedSuccessor : Atlas.StageAtlasZeroToEleven
    localUnitIsStage1 : localUnit ≡ Atlas.atlas-1
    carriedUnitIsStage10 : carriedUnit ≡ Atlas.atlas-10
    joinedSuccessorIsStage11 : joinedSuccessor ≡ Atlas.atlas-11
    unitRoleTransport : SameUnitRoleAcrossScale localUnit carriedUnit

canonicalStageCarryJoin : StageCarryJoin
canonicalStageCarryJoin = record
  { localUnit = Atlas.atlas-1
  ; carriedUnit = Atlas.atlas-10
  ; joinedSuccessor = Atlas.atlas-11
  ; localUnitIsStage1 = refl
  ; carriedUnitIsStage10 = refl
  ; joinedSuccessorIsStage11 = refl
  ; unitRoleTransport = stage1ToStage10UnitLift
  }

------------------------------------------------------------------------
-- Prime-specific branching, 369 diagnostics and the Stage12 atlas remain
-- separate layers of one typed pipeline.
------------------------------------------------------------------------

record PrimeLaneAddressProjection (depth : Nat) : Set where
  field
    primeLane : TP.SSP
    primeSpecificAddressLabel : String
    selected369Address : Ref.Lane369Address depth
    stagePoint : Atlas.StageAtlasZeroToEleven
    primeBranchingIdentifiedWithTernary : Bool
    projectionIsFiniteObservation : Bool
    analyticPAdicCompletionClaimed : Bool
    semanticStageIsArithmeticValueClaimed : Bool

canonicalP3RootProjection : PrimeLaneAddressProjection zero
canonicalP3RootProjection = record
  { primeLane = TP.p3
  ; primeSpecificAddressLabel = "p3-adic root address"
  ; selected369Address = Ref.root
  ; stagePoint = Atlas.atlas-3
  ; primeBranchingIdentifiedWithTernary = false
  ; projectionIsFiniteObservation = true
  ; analyticPAdicCompletionClaimed = false
  ; semanticStageIsArithmeticValueClaimed = false
  }

canonicalP11ThreeSixNineProjection : PrimeLaneAddressProjection 3
canonicalP11ThreeSixNineProjection = record
  { primeLane = TP.p11
  ; primeSpecificAddressLabel = "p11 lane with a selected depth-three 369 diagnostic address"
  ; selected369Address = Ref.canonicalThreeSixNineAddress
  ; stagePoint = Atlas.atlas-11
  ; primeBranchingIdentifiedWithTernary = false
  ; projectionIsFiniteObservation = true
  ; analyticPAdicCompletionClaimed = false
  ; semanticStageIsArithmeticValueClaimed = false
  }

record Prime369StagePipeline : Set₁ where
  field
    PrimeLane : Set
    PrimeAddress : PrimeLane → Set
    Signature369 : Set
    StagePoint : Set
    observe369 : ∀ prime → PrimeAddress prime → Signature369
    interpretStage : Signature369 → StagePoint

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record RadixStageAuthorityBoundary : Set where
  field
    decimalDisplayIsUniversalOntologyClaimed : Bool
    textualLeftPrefixIsAlwaysValuationPrefixClaimed : Bool
    stage1EqualsStage10NumericallyClaimed : Bool
    stage11IsOnlyArithmeticSuccessorClaimed : Bool
    everyPrimeLaneIsTernaryClaimed : Bool
    radixAndScaleOriginAreExplicit : Bool

canonicalRadixStageAuthorityBoundary : RadixStageAuthorityBoundary
canonicalRadixStageAuthorityBoundary = record
  { decimalDisplayIsUniversalOntologyClaimed = false
  ; textualLeftPrefixIsAlwaysValuationPrefixClaimed = false
  ; stage1EqualsStage10NumericallyClaimed = false
  ; stage11IsOnlyArithmeticSuccessorClaimed = false
  ; everyPrimeLaneIsTernaryClaimed = false
  ; radixAndScaleOriginAreExplicit = true
  }

radixStageSummary : String
radixStageSummary =
  "Place value is a coarse/fine geometry: the radix gives weights, the point gives the scale origin, p-adic proximity follows origin-prefix agreement, and Stage 1/10/11 record unit, carry and carry-plus-local-unit roles without arithmetic collapse."
