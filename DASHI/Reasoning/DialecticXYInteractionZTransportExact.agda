module DASHI.Reasoning.DialecticXYInteractionZTransportExact where

------------------------------------------------------------------------
-- THE TWO-DIALECTIC / ONE-INTERACTION 27-CUBE.
--
-- User's original coordinate semantics, NOT a repurposed evidence chart:
--   X = one position of dialectic A: thesis / antithesis / synthesis
--   Y = one position of dialectic B: thesis / antithesis / synthesis
--   Z = one position on the *interaction* between A and B.
--
-- The XY plane is 3×3=9 encounters. Over EACH ordered encounter lie
-- 3 possible Z positions, giving 3×3×3=27 interaction states.
-- No geometry alone selects Z. A declared/qualified synthesis law or
-- a separate witnessed interaction trajectory is required.
--
-- Original canonical owners reused, not copied:
-- * TernaryComparisonSynthesisExact: Comparison9, SynthesisChoice27,
--   comparisonOfSynthesis, synthesisCoordinate, conditional rule.
-- * Base369Ternary27HypervoxelFabricGeometryExact: literal T^3 grid.
-- * TernarySynthesisCellComplexExact: directed comparison/2-cell.
-- Dialectical *role* != truth sign of a proposition; attach each
-- +P/-P/both/neither as a separately keyed, fine evidence fibre.
-- This is neither real legal evidence nor a physical 3-D cube.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Comparison

data DialecticPosition : Set where
  thesis antithesis synthesis : DialecticPosition

positionToTri : DialecticPosition → Base.TriTruth
positionToTri thesis = Base.tri-low
positionToTri antithesis = Base.tri-mid
positionToTri synthesis = Base.tri-high

triToPosition : Base.TriTruth → DialecticPosition
triToPosition Base.tri-low = thesis
triToPosition Base.tri-mid = antithesis
triToPosition Base.tri-high = synthesis

positionTriRoundTrip : (p : DialecticPosition) →
  triToPosition (positionToTri p) ≡ p
positionTriRoundTrip thesis = refl
positionTriRoundTrip antithesis = refl
positionTriRoundTrip synthesis = refl

triPositionRoundTrip : (p : Base.TriTruth) →
  positionToTri (triToPosition p) ≡ p
triPositionRoundTrip Base.tri-low = refl
triPositionRoundTrip Base.tri-mid = refl
triPositionRoundTrip Base.tri-high = refl

positionToTrit : DialecticPosition → SSP.SSPTrit
positionToTrit thesis = SSP.sspNegOne
positionToTrit antithesis = SSP.sspZero
positionToTrit synthesis = SSP.sspPosOne

tritToPosition : SSP.SSPTrit → DialecticPosition
tritToPosition SSP.sspNegOne = thesis
tritToPosition SSP.sspZero = antithesis
tritToPosition SSP.sspPosOne = synthesis

positionTritRoundTrip : (p : DialecticPosition) →
  tritToPosition (positionToTrit p) ≡ p
positionTritRoundTrip thesis = refl
positionTritRoundTrip antithesis = refl
positionTritRoundTrip synthesis = refl

tritPositionRoundTrip : (t : SSP.SSPTrit) →
  positionToTrit (tritToPosition t) ≡ t
tritPositionRoundTrip SSP.sspNegOne = refl
tritPositionRoundTrip SSP.sspZero = refl
tritPositionRoundTrip SSP.sspPosOne = refl

record DialecticEncounter27 : Set where
  constructor dialectic-encounter
  field
    xDialecticPosition : DialecticPosition
    yDialecticPosition : DialecticPosition
    zInteractionPosition : DialecticPosition
open DialecticEncounter27 public

toCanonicalComparison27 : DialecticEncounter27 →
  Comparison.SynthesisChoice27
toCanonicalComparison27 cell =
  Comparison.makeSynthesisChoice
    (positionToTri (xDialecticPosition cell))
    (positionToTri (yDialecticPosition cell))
    (positionToTri (zInteractionPosition cell))

fromCanonicalComparison27 : Comparison.SynthesisChoice27 →
  DialecticEncounter27
fromCanonicalComparison27 (x , (y , z)) =
  dialectic-encounter
    (triToPosition x)
    (triToPosition y)
    (triToPosition z)

canonicalComparisonRoundTrip : (cell : DialecticEncounter27) →
  fromCanonicalComparison27 (toCanonicalComparison27 cell) ≡ cell
canonicalComparisonRoundTrip
  (dialectic-encounter thesis thesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis thesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis thesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis antithesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis antithesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis antithesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis synthesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis synthesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter thesis synthesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis thesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis thesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis thesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis antithesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis antithesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis antithesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis synthesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis synthesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter antithesis synthesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis thesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis thesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis thesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis antithesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis antithesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis antithesis synthesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis synthesis thesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis synthesis antithesis) = refl
canonicalComparisonRoundTrip
  (dialectic-encounter synthesis synthesis synthesis) = refl

comparisonCanonicalRoundTrip : (c : Comparison.SynthesisChoice27) →
  toCanonicalComparison27 (fromCanonicalComparison27 c) ≡ c
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
comparisonCanonicalRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

toCanonicalCube : DialecticEncounter27 → Cube.Ternary27Point
toCanonicalCube cell = Cube.ternary27Point
  (positionToTrit (xDialecticPosition cell))
  (positionToTrit (yDialecticPosition cell))
  (positionToTrit (zInteractionPosition cell))

fromCanonicalCube : Cube.Ternary27Point → DialecticEncounter27
fromCanonicalCube (Cube.ternary27Point x y z) =
  dialectic-encounter
    (tritToPosition x)
    (tritToPosition y)
    (tritToPosition z)

cubePositionRoundTrip : (cell : DialecticEncounter27) →
  fromCanonicalCube (toCanonicalCube cell) ≡ cell
cubePositionRoundTrip (dialectic-encounter x y z)
  rewrite positionTritRoundTrip x
        | positionTritRoundTrip y
        | positionTritRoundTrip z = refl

positionCubeRoundTrip : (cube : Cube.Ternary27Point) →
  toCanonicalCube (fromCanonicalCube cube) ≡ cube
positionCubeRoundTrip (Cube.ternary27Point x y z)
  rewrite tritPositionRoundTrip x
        | tritPositionRoundTrip y
        | tritPositionRoundTrip z = refl

-- X and Y specify the comparison plane, exactly 3x3=9 choices.
-- Z is independent until a separately supplied interaction law picks it.
xyEncounter : DialecticEncounter27 → DialecticPosition × DialecticPosition
xyEncounter cell = xDialecticPosition cell , yDialecticPosition cell

zCannotBeDerivedFromXYAlone :
  (choose : DialecticPosition × DialecticPosition → DialecticPosition) →
  ((cell : DialecticEncounter27) →
    choose (xyEncounter cell) ≡ zInteractionPosition cell) → ⊥
zCannotBeDerivedFromXYAlone choose all =
  impossible
    (sym (all (dialectic-encounter thesis antithesis thesis)))
    (all (dialectic-encounter thesis antithesis antithesis)))
  where
    impossible : (choose (thesis , antithesis) ≡ thesis) →
      (choose (thesis , antithesis) ≡ antithesis) → ⊥
    impossible one two with trans (sym one) two
    ... | ()

-- A total declared transport SELECTS Z and is exactly a rule, not a
-- topology-implied value or an actual empirical/logical authority.
record DialecticInteractionRule : Set where
  constructor dialectic-interaction-rule
  field
    chosenZ : DialecticPosition → DialecticPosition → DialecticPosition
open DialecticInteractionRule public

transportXY : DialecticInteractionRule →
  (x y : DialecticPosition) → DialecticEncounter27
transportXY rule x y = dialectic-encounter x y (chosenZ rule x y)

transportRetainsX : (rule : DialecticInteractionRule)
  (x y : DialecticPosition) →
  xDialecticPosition (transportXY rule x y) ≡ x
transportRetainsX rule x y = refl

transportRetainsY : (rule : DialecticInteractionRule)
  (x y : DialecticPosition) →
  yDialecticPosition (transportXY rule x y) ≡ y
transportRetainsY rule x y = refl

transportRespectsZRule : (rule : DialecticInteractionRule)
  (x y : DialecticPosition) →
  zInteractionPosition (transportXY rule x y) ≡ chosenZ rule x y
transportRespectsZRule rule x y = refl

-- A within-column evolution preserves the two input dialectic
-- positions while allowing the interaction to move along Z.
data InteractionZStep : DialecticEncounter27 → DialecticEncounter27 → Set where
  thesisToAntithesis : ∀ {x y} →
    InteractionZStep
      (dialectic-encounter x y thesis)
      (dialectic-encounter x y antithesis)
  antithesisToSynthesis : ∀ {x y} →
    InteractionZStep
      (dialectic-encounter x y antithesis)
      (dialectic-encounter x y synthesis)

illustrativeTwoStep :
  InteractionZStep
    (dialectic-encounter thesis antithesis thesis)
    (dialectic-encounter thesis antithesis antithesis)
  ×
  InteractionZStep
    (dialectic-encounter thesis antithesis antithesis)
    (dialectic-encounter thesis antithesis synthesis)
illustrativeTwoStep =
  thesisToAntithesis , antithesisToSynthesis

-- These are permitted phase moves, not an empirical claim that all
-- dialectics evolve monotonically or that synthesis is unavoidable.
carrierPositionCount : Nat
carrierPositionCount = Comparison.synthesisChoiceDimension

carrierPositionCountIs27 : carrierPositionCount ≡ 27
carrierPositionCountIs27 = Comparison.synthesisChoiceDimensionIsTwentySeven
