module DASHI.Physics.YangMills.BalabanPath4AverageJensenExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)

------------------------------------------------------------------------
-- Exact four-point Jensen/SOS identity.
--
-- Repeating a four-point average four times costs no more square energy than
-- the original four values:
--
--   4 ((a+b+c+d)/4)^2 <= a^2+b^2+c^2+d^2.
--
-- The discarded remainder is one quarter of the six pairwise difference
-- squares, so the inequality is constructive and rational.
------------------------------------------------------------------------

twoℚ fourℚ quarter : ℚ
twoℚ = 1ℚ + 1ℚ
fourℚ = twoℚ + twoℚ
quarter = + 1 / 4

fourPointSum : ℚ → ℚ → ℚ → ℚ → ℚ
fourPointSum a b c d = a + (b + (c + d))

fourPointAverage : ℚ → ℚ → ℚ → ℚ → ℚ
fourPointAverage a b c d = quarter * fourPointSum a b c d

fourPointSquareEnergy : ℚ → ℚ → ℚ → ℚ → ℚ
fourPointSquareEnergy a b c d =
  sq a + (sq b + (sq c + sq d))

sixPairDifferenceSquares : ℚ → ℚ → ℚ → ℚ → ℚ
sixPairDifferenceSquares a b c d =
  sqDiff a b
  + (sqDiff a c
  + (sqDiff a d
  + (sqDiff b c
  + (sqDiff b d + sqDiff c d))))

fourPointJensenIdentity : ∀ a b c d →
  fourPointSquareEnergy a b c d
  ≡ fourℚ * sq (fourPointAverage a b c d)
    + quarter * sixPairDifferenceSquares a b c d
fourPointJensenIdentity = ℚRing.solve-∀

sixPairDifferenceSquaresNonnegative : ∀ a b c d →
  0ℚ ≤ sixPairDifferenceSquares a b c d
sixPairDifferenceSquaresNonnegative a b c d =
  ℚP.+-mono-≤
    (squareNonnegative (a + (- b)))
    (ℚP.+-mono-≤
      (squareNonnegative (a + (- c)))
      (ℚP.+-mono-≤
        (squareNonnegative (a + (- d)))
        (ℚP.+-mono-≤
          (squareNonnegative (b + (- c)))
          (ℚP.+-mono-≤
            (squareNonnegative (b + (- d)))
            (squareNonnegative (c + (- d)))))))

quarterNonnegative : 0ℚ ≤ quarter
quarterNonnegative =
  let
    instance
      quarterNonnegativeInstance : NonNegative quarter
      quarterNonnegativeInstance = ℚP.normalize-nonNeg 1 4
  in
  ℚP.nonNegative⁻¹ quarter

jensenRemainderNonnegative : ∀ a b c d →
  0ℚ ≤ quarter * sixPairDifferenceSquares a b c d
jensenRemainderNonnegative a b c d =
  let
    instance
      quarterNonnegativeInstance : NonNegative quarter
      quarterNonnegativeInstance = nonNegative quarterNonnegative

      differenceSumNonnegativeInstance :
        NonNegative (sixPairDifferenceSquares a b c d)
      differenceSumNonnegativeInstance =
        nonNegative (sixPairDifferenceSquaresNonnegative a b c d)

      productNonnegative :
        NonNegative (quarter * sixPairDifferenceSquares a b c d)
      productNonnegative =
        ℚP.nonNeg*nonNeg⇒nonNeg quarter
          (sixPairDifferenceSquares a b c d)
  in
  ℚP.nonNegative⁻¹
    (quarter * sixPairDifferenceSquares a b c d)

fourPointAverageEnergyContraction : ∀ a b c d →
  fourℚ * sq (fourPointAverage a b c d)
  ≤ fourPointSquareEnergy a b c d
fourPointAverageEnergyContraction a b c d =
  subst
    (λ upper →
      fourℚ * sq (fourPointAverage a b c d) ≤ upper)
    (sym (fourPointJensenIdentity a b c d))
    (baseBelowBasePlusRemainder
      (fourℚ * sq (fourPointAverage a b c d))
      (quarter * sixPairDifferenceSquares a b c d)
      (jensenRemainderNonnegative a b c d))

------------------------------------------------------------------------
-- Finite family of four-point groups.
------------------------------------------------------------------------

record FourValues : Set where
  constructor fourValues
  field
    value0 value1 value2 value3 : ℚ

open FourValues public

groupAverageEnergy group =
  fourℚ * sq
    (fourPointAverage
      (value0 group) (value1 group) (value2 group) (value3 group))

groupOriginalEnergy group =
  fourPointSquareEnergy
    (value0 group) (value1 group) (value2 group) (value3 group)

groupAverageEnergyContraction : ∀ group →
  groupAverageEnergy group ≤ groupOriginalEnergy group
groupAverageEnergyContraction group =
  fourPointAverageEnergyContraction
    (value0 group) (value1 group) (value2 group) (value3 group)

sumGroupAverageEnergy : List FourValues → ℚ
sumGroupAverageEnergy groups = sumRational groups groupAverageEnergy

sumGroupOriginalEnergy : List FourValues → ℚ
sumGroupOriginalEnergy groups = sumRational groups groupOriginalEnergy

finiteGroupedAverageEnergyContraction : ∀ groups →
  sumGroupAverageEnergy groups ≤ sumGroupOriginalEnergy groups
finiteGroupedAverageEnergyContraction [] = ℚP.≤-refl
finiteGroupedAverageEnergyContraction (group ∷ groups) =
  ℚP.+-mono-≤
    (groupAverageEnergyContraction group)
    (finiteGroupedAverageEnergyContraction groups)

fourPointJensenSOSLevel : ProofLevel
fourPointJensenSOSLevel = computed

fourPointAverageEnergyContractionLevel : ProofLevel
fourPointAverageEnergyContractionLevel = machineChecked

finiteGroupedAverageEnergyContractionLevel : ProofLevel
finiteGroupedAverageEnergyContractionLevel = machineChecked

physicalAxisAverageDirectionalGroupingLevel : ProofLevel
physicalAxisAverageDirectionalGroupingLevel = conditional
