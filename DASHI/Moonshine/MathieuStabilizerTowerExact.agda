module DASHI.Moonshine.MathieuStabilizerTowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- and Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- No DOI assigned.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Record the textbook explanation of the Mathieu orders:
--
--   |M11| = 11 falling 4 = 11 * 10 * 9 * 8 = 7920
--   |M12| = 12 falling 5 = 12 * 11 * 10 * 9 * 8 = 95040.
--
-- These products are forced by sharp 4-transitivity and sharp
-- 5-transitivity respectively.  They are not reconstructed from D4, a
-- nine-cell grid, a divisor lattice, or numeral coincidences.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Falling factorials count ordered tuples of distinct points.
------------------------------------------------------------------------

fallingFactorial : Nat → Nat → Nat
fallingFactorial n zero = 1
fallingFactorial n (suc k) = n * fallingFactorial (n ∸ 1) k

orderedDistinctFourTuplesOnEleven : Nat
orderedDistinctFourTuplesOnEleven = fallingFactorial 11 4

orderedDistinctFiveTuplesOnTwelve : Nat
orderedDistinctFiveTuplesOnTwelve = fallingFactorial 12 5

orderedDistinctFourTuplesOnElevenIs7920 :
  orderedDistinctFourTuplesOnEleven ≡ 7920
orderedDistinctFourTuplesOnElevenIs7920 = refl

orderedDistinctFiveTuplesOnTwelveIs95040 :
  orderedDistinctFiveTuplesOnTwelve ≡ 95040
orderedDistinctFiveTuplesOnTwelveIs95040 = refl

------------------------------------------------------------------------
-- Sharp transitivity order principle.
--
-- A sharply k-transitive action is free and transitive on ordered distinct
-- k-tuples.  Therefore each group element corresponds to exactly one image
-- of a fixed ordered k-tuple, and the group order is n falling k.
--
-- This record stores the resulting order theorem as source-bounded data.  It
-- does not manufacture the permutation action itself.
------------------------------------------------------------------------

record SharpTransitivityOrderWitness : Set where
  constructor sharpTransitivityOrderWitness
  field
    pointCount : Nat
    transitivityDegree : Nat
    groupOrder : Nat
    sharpOrderLaw :
      groupOrder ≡ fallingFactorial pointCount transitivityDegree

open SharpTransitivityOrderWitness public

m11SharpFourOrderWitness : SharpTransitivityOrderWitness
m11SharpFourOrderWitness =
  sharpTransitivityOrderWitness 11 4 7920 refl

m12SharpFiveOrderWitness : SharpTransitivityOrderWitness
m12SharpFiveOrderWitness =
  sharpTransitivityOrderWitness 12 5 95040 refl

m11OrderFromSharpFourTransitivity :
  groupOrder m11SharpFourOrderWitness ≡ 11 * 10 * 9 * 8
m11OrderFromSharpFourTransitivity = refl

m12OrderFromSharpFiveTransitivity :
  groupOrder m12SharpFiveOrderWitness ≡ 12 * 11 * 10 * 9 * 8
m12OrderFromSharpFiveTransitivity = refl

------------------------------------------------------------------------
-- Successive stabilizer orders.
--
-- Fixing one more entry of an ordered tuple divides the remaining sharp
-- action by the number of available images.  Reading from the deepest
-- stabilizer upward gives 8 -> 72 -> 720 -> 7920 -> 95040.
------------------------------------------------------------------------

data MathieuLevel : Set where
  M8Level M9Level M10Level M11Level M12Level : MathieuLevel

levelOrder : MathieuLevel → Nat
levelOrder M8Level = 8
levelOrder M9Level = 72
levelOrder M10Level = 720
levelOrder M11Level = 7920
levelOrder M12Level = 95040

record StabilizerStep : Set where
  constructor stabilizerStep
  field
    lowerLevel : MathieuLevel
    upperLevel : MathieuLevel
    availableImages : Nat
    orderLaw :
      levelOrder upperLevel
      ≡ availableImages * levelOrder lowerLevel

open StabilizerStep public

step8To9 : StabilizerStep
step8To9 = stabilizerStep M8Level M9Level 9 refl

step9To10 : StabilizerStep
step9To10 = stabilizerStep M9Level M10Level 10 refl

step10To11 : StabilizerStep
step10To11 = stabilizerStep M10Level M11Level 11 refl

step11To12 : StabilizerStep
step11To12 = stabilizerStep M11Level M12Level 12 refl

m11OrderAsSuccessivePointChoices :
  levelOrder M11Level ≡ 11 * 10 * 9 * 8
m11OrderAsSuccessivePointChoices = refl

m12OrderAsSuccessivePointChoices :
  levelOrder M12Level ≡ 12 * 11 * 10 * 9 * 8
m12OrderAsSuccessivePointChoices = refl

m11OrderAsPreviousDisplayOrder :
  levelOrder M11Level ≡ 8 * 9 * 10 * 11
m11OrderAsPreviousDisplayOrder = refl

m12OrderAsPreviousDisplayOrder :
  levelOrder M12Level ≡ 8 * 9 * 10 * 11 * 12
m12OrderAsPreviousDisplayOrder = refl

threePointStabilizerOrderInM11 : Nat
threePointStabilizerOrderInM11 = fallingFactorial 8 1

threePointStabilizerOrderInM11IsEight :
  threePointStabilizerOrderInM11 ≡ 8
threePointStabilizerOrderInM11IsEight = refl

------------------------------------------------------------------------
-- Anti-numerology boundary.
------------------------------------------------------------------------

data SourceOfEight : Set where
  remainingImagesAfterFixingThreePoints
  squareGridDihedralOrder
  unrelatedOrderEightObject : SourceOfEight

mathieuEightSource : SourceOfEight
mathieuEightSource = remainingImagesAfterFixingThreePoints

mathieuEightDoesNotComeFromD4 :
  mathieuEightSource ≡ squareGridDihedralOrder → ⊥
mathieuEightDoesNotComeFromD4 ()

record MathieuTowerBoundary : Set where
  constructor mathieuTowerBoundary
  field
    m11OrderForcedBySharpFourTransitivity : Bool
    m11OrderForcedBySharpFourTransitivityIsTrue :
      m11OrderForcedBySharpFourTransitivity ≡ true
    m12OrderForcedBySharpFiveTransitivity : Bool
    m12OrderForcedBySharpFiveTransitivityIsTrue :
      m12OrderForcedBySharpFiveTransitivity ≡ true
    factorEightComesFromD4GridSymmetry : Bool
    factorEightComesFromD4GridSymmetryIsFalse :
      factorEightComesFromD4GridSymmetry ≡ false
    divisorLatticeNeededToDeriveOrders : Bool
    divisorLatticeNeededToDeriveOrdersIsFalse :
      divisorLatticeNeededToDeriveOrders ≡ false
    actualPermutationActionsConstructedHere : Bool
    actualPermutationActionsConstructedHereIsFalse :
      actualPermutationActionsConstructedHere ≡ false
    equalNumeralsImplySharedStructuralCause : Bool
    equalNumeralsImplySharedStructuralCauseIsFalse :
      equalNumeralsImplySharedStructuralCause ≡ false

canonicalMathieuTowerBoundary : MathieuTowerBoundary
canonicalMathieuTowerBoundary =
  mathieuTowerBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
