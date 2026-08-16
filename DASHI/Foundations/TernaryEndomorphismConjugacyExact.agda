module DASHI.Foundations.TernaryEndomorphismConjugacyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups", Mathematical Surveys and Monographs 117,
-- American Mathematical Society, 2005.
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
--
-- Equip the repository's existing 27 ternary level-two codes with the six
-- actual coordinate permutations of TriTruth. These are the reversible codes.
-- Conjugation classifies all 27 endomorphisms into seven functional-graph
-- shapes. Every code carries an explicit permutation witness placing it in
-- one of the seven representative orbits, and no representative orbit changes
-- class under any of the six reorientations.
--
-- "Seven shapes" means seven conjugation-orbit archetypes, NOT seven
-- irreducible representations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)

import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower

data TriPermutation : Set where
  permIdentity
    permRotate
    permRotate2
    permSwapLowMid
    permSwapLowHigh
    permSwapMidHigh : TriPermutation

applyPermutation : TriPermutation → Base.TriTruth → Base.TriTruth
applyPermutation permIdentity value = value
applyPermutation permRotate Base.tri-low = Base.tri-mid
applyPermutation permRotate Base.tri-mid = Base.tri-high
applyPermutation permRotate Base.tri-high = Base.tri-low
applyPermutation permRotate2 Base.tri-low = Base.tri-high
applyPermutation permRotate2 Base.tri-mid = Base.tri-low
applyPermutation permRotate2 Base.tri-high = Base.tri-mid
applyPermutation permSwapLowMid Base.tri-low = Base.tri-mid
applyPermutation permSwapLowMid Base.tri-mid = Base.tri-low
applyPermutation permSwapLowMid Base.tri-high = Base.tri-high
applyPermutation permSwapLowHigh Base.tri-low = Base.tri-high
applyPermutation permSwapLowHigh Base.tri-mid = Base.tri-mid
applyPermutation permSwapLowHigh Base.tri-high = Base.tri-low
applyPermutation permSwapMidHigh Base.tri-low = Base.tri-low
applyPermutation permSwapMidHigh Base.tri-mid = Base.tri-high
applyPermutation permSwapMidHigh Base.tri-high = Base.tri-mid

inversePermutation : TriPermutation → TriPermutation
inversePermutation permIdentity = permIdentity
inversePermutation permRotate = permRotate2
inversePermutation permRotate2 = permRotate
inversePermutation permSwapLowMid = permSwapLowMid
inversePermutation permSwapLowHigh = permSwapLowHigh
inversePermutation permSwapMidHigh = permSwapMidHigh

inverseLeftAt :
  (permutation : TriPermutation) →
  (value : Base.TriTruth) →
  applyPermutation (inversePermutation permutation)
    (applyPermutation permutation value)
  ≡ value
inverseLeftAt permIdentity value = refl
inverseLeftAt permRotate Base.tri-low = refl
inverseLeftAt permRotate Base.tri-mid = refl
inverseLeftAt permRotate Base.tri-high = refl
inverseLeftAt permRotate2 Base.tri-low = refl
inverseLeftAt permRotate2 Base.tri-mid = refl
inverseLeftAt permRotate2 Base.tri-high = refl
inverseLeftAt permSwapLowMid Base.tri-low = refl
inverseLeftAt permSwapLowMid Base.tri-mid = refl
inverseLeftAt permSwapLowMid Base.tri-high = refl
inverseLeftAt permSwapLowHigh Base.tri-low = refl
inverseLeftAt permSwapLowHigh Base.tri-mid = refl
inverseLeftAt permSwapLowHigh Base.tri-high = refl
inverseLeftAt permSwapMidHigh Base.tri-low = refl
inverseLeftAt permSwapMidHigh Base.tri-mid = refl
inverseLeftAt permSwapMidHigh Base.tri-high = refl

inverseRightAt :
  (permutation : TriPermutation) →
  (value : Base.TriTruth) →
  applyPermutation permutation
    (applyPermutation (inversePermutation permutation) value)
  ≡ value
inverseRightAt permIdentity value = refl
inverseRightAt permRotate Base.tri-low = refl
inverseRightAt permRotate Base.tri-mid = refl
inverseRightAt permRotate Base.tri-high = refl
inverseRightAt permRotate2 Base.tri-low = refl
inverseRightAt permRotate2 Base.tri-mid = refl
inverseRightAt permRotate2 Base.tri-high = refl
inverseRightAt permSwapLowMid Base.tri-low = refl
inverseRightAt permSwapLowMid Base.tri-mid = refl
inverseRightAt permSwapLowMid Base.tri-high = refl
inverseRightAt permSwapLowHigh Base.tri-low = refl
inverseRightAt permSwapLowHigh Base.tri-mid = refl
inverseRightAt permSwapLowHigh Base.tri-high = refl
inverseRightAt permSwapMidHigh Base.tri-low = refl
inverseRightAt permSwapMidHigh Base.tri-mid = refl
inverseRightAt permSwapMidHigh Base.tri-high = refl

permutationCode : TriPermutation → Tower.LevelTwoCode
permutationCode permutation =
  applyPermutation permutation Base.tri-low ,
  (applyPermutation permutation Base.tri-mid ,
   applyPermutation permutation Base.tri-high)

identityCode : Tower.LevelTwoCode
identityCode = permutationCode permIdentity

composeCode :
  Tower.LevelTwoCode → Tower.LevelTwoCode → Tower.LevelTwoCode
composeCode left right =
  Tower.encodeLevelTwo
    (λ input →
      Tower.decodeLevelTwo left
        (Tower.decodeLevelTwo right input))

permutationInverseCodeLeft :
  (permutation : TriPermutation) →
  composeCode
    (permutationCode (inversePermutation permutation))
    (permutationCode permutation)
  ≡ identityCode
permutationInverseCodeLeft permIdentity = refl
permutationInverseCodeLeft permRotate = refl
permutationInverseCodeLeft permRotate2 = refl
permutationInverseCodeLeft permSwapLowMid = refl
permutationInverseCodeLeft permSwapLowHigh = refl
permutationInverseCodeLeft permSwapMidHigh = refl

permutationInverseCodeRight :
  (permutation : TriPermutation) →
  composeCode
    (permutationCode permutation)
    (permutationCode (inversePermutation permutation))
  ≡ identityCode
permutationInverseCodeRight permIdentity = refl
permutationInverseCodeRight permRotate = refl
permutationInverseCodeRight permRotate2 = refl
permutationInverseCodeRight permSwapLowMid = refl
permutationInverseCodeRight permSwapLowHigh = refl
permutationInverseCodeRight permSwapMidHigh = refl

conjugateCode :
  TriPermutation → Tower.LevelTwoCode → Tower.LevelTwoCode
conjugateCode permutation code =
  Tower.encodeLevelTwo
    (λ input →
      applyPermutation permutation
        (Tower.decodeLevelTwo code
          (applyPermutation (inversePermutation permutation) input)))

data ShapeOrbit7 : Set where
  identityShape
    threeCycleShape
    transpositionShape
    constantShape
    rank2OneFixedShape
    rank2TwoFixedShape
    rank2TwoCycleShape : ShapeOrbit7

shapeClass : Tower.LevelTwoCode → ShapeOrbit7
shapeClass (Base.tri-low , (Base.tri-low , Base.tri-low)) = constantShape
shapeClass (Base.tri-low , (Base.tri-low , Base.tri-mid)) = rank2OneFixedShape
shapeClass (Base.tri-low , (Base.tri-low , Base.tri-high)) = rank2TwoFixedShape
shapeClass (Base.tri-low , (Base.tri-mid , Base.tri-low)) = rank2TwoFixedShape
shapeClass (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = rank2TwoFixedShape
shapeClass (Base.tri-low , (Base.tri-mid , Base.tri-high)) = identityShape
shapeClass (Base.tri-low , (Base.tri-high , Base.tri-low)) = rank2OneFixedShape
shapeClass (Base.tri-low , (Base.tri-high , Base.tri-mid)) = transpositionShape
shapeClass (Base.tri-low , (Base.tri-high , Base.tri-high)) = rank2TwoFixedShape
shapeClass (Base.tri-mid , (Base.tri-low , Base.tri-low)) = rank2TwoCycleShape
shapeClass (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = rank2TwoCycleShape
shapeClass (Base.tri-mid , (Base.tri-low , Base.tri-high)) = transpositionShape
shapeClass (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = rank2OneFixedShape
shapeClass (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = constantShape
shapeClass (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = rank2TwoFixedShape
shapeClass (Base.tri-mid , (Base.tri-high , Base.tri-low)) = threeCycleShape
shapeClass (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = rank2TwoCycleShape
shapeClass (Base.tri-mid , (Base.tri-high , Base.tri-high)) = rank2OneFixedShape
shapeClass (Base.tri-high , (Base.tri-low , Base.tri-low)) = rank2TwoCycleShape
shapeClass (Base.tri-high , (Base.tri-low , Base.tri-mid)) = threeCycleShape
shapeClass (Base.tri-high , (Base.tri-low , Base.tri-high)) = rank2OneFixedShape
shapeClass (Base.tri-high , (Base.tri-mid , Base.tri-low)) = transpositionShape
shapeClass (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = rank2OneFixedShape
shapeClass (Base.tri-high , (Base.tri-mid , Base.tri-high)) = rank2TwoFixedShape
shapeClass (Base.tri-high , (Base.tri-high , Base.tri-low)) = rank2TwoCycleShape
shapeClass (Base.tri-high , (Base.tri-high , Base.tri-mid)) = rank2TwoCycleShape
shapeClass (Base.tri-high , (Base.tri-high , Base.tri-high)) = constantShape

shapeRepresentative : ShapeOrbit7 → Tower.LevelTwoCode
shapeRepresentative identityShape =
  Base.tri-low , (Base.tri-mid , Base.tri-high)
shapeRepresentative threeCycleShape =
  Base.tri-mid , (Base.tri-high , Base.tri-low)
shapeRepresentative transpositionShape =
  Base.tri-low , (Base.tri-high , Base.tri-mid)
shapeRepresentative constantShape =
  Base.tri-low , (Base.tri-low , Base.tri-low)
shapeRepresentative rank2OneFixedShape =
  Base.tri-low , (Base.tri-low , Base.tri-mid)
shapeRepresentative rank2TwoFixedShape =
  Base.tri-low , (Base.tri-low , Base.tri-high)
shapeRepresentative rank2TwoCycleShape =
  Base.tri-mid , (Base.tri-low , Base.tri-low)

representativeHasDeclaredShape :
  (shape : ShapeOrbit7) →
  shapeClass (shapeRepresentative shape) ≡ shape
representativeHasDeclaredShape identityShape = refl
representativeHasDeclaredShape threeCycleShape = refl
representativeHasDeclaredShape transpositionShape = refl
representativeHasDeclaredShape constantShape = refl
representativeHasDeclaredShape rank2OneFixedShape = refl
representativeHasDeclaredShape rank2TwoFixedShape = refl
representativeHasDeclaredShape rank2TwoCycleShape = refl

data OrbitWitness
    (shape : ShapeOrbit7)
    (code : Tower.LevelTwoCode) : Set where
  orbitWitness :
    (permutation : TriPermutation) →
    code ≡ conjugateCode permutation (shapeRepresentative shape) →
    OrbitWitness shape code

canonicalOrbitWitness :
  (code : Tower.LevelTwoCode) →
  OrbitWitness (shapeClass code) code
canonicalOrbitWitness (Base.tri-low , (Base.tri-low , Base.tri-low)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-low , Base.tri-mid)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-low , Base.tri-high)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-mid , Base.tri-low)) = orbitWitness permSwapMidHigh refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = orbitWitness permRotate refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-mid , Base.tri-high)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-high , Base.tri-low)) = orbitWitness permSwapMidHigh refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-high , Base.tri-mid)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-low , (Base.tri-high , Base.tri-high)) = orbitWitness permSwapLowHigh refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-low , Base.tri-low)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = orbitWitness permSwapLowMid refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-low , Base.tri-high)) = orbitWitness permRotate2 refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = orbitWitness permSwapLowMid refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = orbitWitness permRotate refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = orbitWitness permSwapLowMid refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-high , Base.tri-low)) = orbitWitness permIdentity refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = orbitWitness permRotate refl
canonicalOrbitWitness (Base.tri-mid , (Base.tri-high , Base.tri-high)) = orbitWitness permSwapLowHigh refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-low , Base.tri-low)) = orbitWitness permSwapMidHigh refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-low , Base.tri-mid)) = orbitWitness permSwapLowMid refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-low , Base.tri-high)) = orbitWitness permRotate2 refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-mid , Base.tri-low)) = orbitWitness permRotate refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = orbitWitness permRotate refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-mid , Base.tri-high)) = orbitWitness permRotate2 refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-high , Base.tri-low)) = orbitWitness permRotate2 refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-high , Base.tri-mid)) = orbitWitness permSwapLowHigh refl
canonicalOrbitWitness (Base.tri-high , (Base.tri-high , Base.tri-high)) = orbitWitness permRotate2 refl

representativeOrbitStaysClass :
  (permutation : TriPermutation) →
  (shape : ShapeOrbit7) →
  shapeClass (conjugateCode permutation (shapeRepresentative shape))
  ≡ shape
representativeOrbitStaysClass permIdentity identityShape = refl
representativeOrbitStaysClass permIdentity threeCycleShape = refl
representativeOrbitStaysClass permIdentity transpositionShape = refl
representativeOrbitStaysClass permIdentity constantShape = refl
representativeOrbitStaysClass permIdentity rank2OneFixedShape = refl
representativeOrbitStaysClass permIdentity rank2TwoFixedShape = refl
representativeOrbitStaysClass permIdentity rank2TwoCycleShape = refl
representativeOrbitStaysClass permRotate identityShape = refl
representativeOrbitStaysClass permRotate threeCycleShape = refl
representativeOrbitStaysClass permRotate transpositionShape = refl
representativeOrbitStaysClass permRotate constantShape = refl
representativeOrbitStaysClass permRotate rank2OneFixedShape = refl
representativeOrbitStaysClass permRotate rank2TwoFixedShape = refl
representativeOrbitStaysClass permRotate rank2TwoCycleShape = refl
representativeOrbitStaysClass permRotate2 identityShape = refl
representativeOrbitStaysClass permRotate2 threeCycleShape = refl
representativeOrbitStaysClass permRotate2 transpositionShape = refl
representativeOrbitStaysClass permRotate2 constantShape = refl
representativeOrbitStaysClass permRotate2 rank2OneFixedShape = refl
representativeOrbitStaysClass permRotate2 rank2TwoFixedShape = refl
representativeOrbitStaysClass permRotate2 rank2TwoCycleShape = refl
representativeOrbitStaysClass permSwapLowMid identityShape = refl
representativeOrbitStaysClass permSwapLowMid threeCycleShape = refl
representativeOrbitStaysClass permSwapLowMid transpositionShape = refl
representativeOrbitStaysClass permSwapLowMid constantShape = refl
representativeOrbitStaysClass permSwapLowMid rank2OneFixedShape = refl
representativeOrbitStaysClass permSwapLowMid rank2TwoFixedShape = refl
representativeOrbitStaysClass permSwapLowMid rank2TwoCycleShape = refl
representativeOrbitStaysClass permSwapLowHigh identityShape = refl
representativeOrbitStaysClass permSwapLowHigh threeCycleShape = refl
representativeOrbitStaysClass permSwapLowHigh transpositionShape = refl
representativeOrbitStaysClass permSwapLowHigh constantShape = refl
representativeOrbitStaysClass permSwapLowHigh rank2OneFixedShape = refl
representativeOrbitStaysClass permSwapLowHigh rank2TwoFixedShape = refl
representativeOrbitStaysClass permSwapLowHigh rank2TwoCycleShape = refl
representativeOrbitStaysClass permSwapMidHigh identityShape = refl
representativeOrbitStaysClass permSwapMidHigh threeCycleShape = refl
representativeOrbitStaysClass permSwapMidHigh transpositionShape = refl
representativeOrbitStaysClass permSwapMidHigh constantShape = refl
representativeOrbitStaysClass permSwapMidHigh rank2OneFixedShape = refl
representativeOrbitStaysClass permSwapMidHigh rank2TwoFixedShape = refl
representativeOrbitStaysClass permSwapMidHigh rank2TwoCycleShape = refl

shapeOrbitSize : ShapeOrbit7 → Nat
shapeOrbitSize identityShape = 1
shapeOrbitSize threeCycleShape = 2
shapeOrbitSize transpositionShape = 3
shapeOrbitSize constantShape = 3
shapeOrbitSize rank2OneFixedShape = 6
shapeOrbitSize rank2TwoFixedShape = 6
shapeOrbitSize rank2TwoCycleShape = 6

allShapeOrbits : List ShapeOrbit7
allShapeOrbits =
  identityShape
  ∷ threeCycleShape
  ∷ transpositionShape
  ∷ constantShape
  ∷ rank2OneFixedShape
  ∷ rank2TwoFixedShape
  ∷ rank2TwoCycleShape
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

shapeOrbitCountIsSeven : listCount allShapeOrbits ≡ 7
shapeOrbitCountIsSeven = refl

shapeOrbitSizesSumToTwentySeven :
  shapeOrbitSize identityShape
  + shapeOrbitSize threeCycleShape
  + shapeOrbitSize transpositionShape
  + shapeOrbitSize constantShape
  + shapeOrbitSize rank2OneFixedShape
  + shapeOrbitSize rank2TwoFixedShape
  + shapeOrbitSize rank2TwoCycleShape
  ≡ 27
shapeOrbitSizesSumToTwentySeven = refl

unitShapeSectorIsSix :
  shapeOrbitSize identityShape
  + shapeOrbitSize threeCycleShape
  + shapeOrbitSize transpositionShape
  ≡ 6
unitShapeSectorIsSix = refl

nonUnitShapeSectorIsTwentyOne :
  shapeOrbitSize constantShape
  + shapeOrbitSize rank2OneFixedShape
  + shapeOrbitSize rank2TwoFixedShape
  + shapeOrbitSize rank2TwoCycleShape
  ≡ 21
nonUnitShapeSectorIsTwentyOne = refl

record TernaryConjugacyBoundary : Set where
  field
    sixReversibleCoordinateMapsConstructed : Bool
    sixReversibleCoordinateMapsConstructedIsTrue :
      sixReversibleCoordinateMapsConstructed ≡ true

    sevenConjugacyShapesConstructed : Bool
    sevenConjugacyShapesConstructedIsTrue :
      sevenConjugacyShapesConstructed ≡ true

    sevenMeansIrreducibleRepresentations : Bool
    sevenMeansIrreducibleRepresentationsIsFalse :
      sevenMeansIrreducibleRepresentations ≡ false

canonicalTernaryConjugacyBoundary : TernaryConjugacyBoundary
canonicalTernaryConjugacyBoundary =
  record
    { sixReversibleCoordinateMapsConstructed = true
    ; sixReversibleCoordinateMapsConstructedIsTrue = refl
    ; sevenConjugacyShapesConstructed = true
    ; sevenConjugacyShapesConstructedIsTrue = refl
    ; sevenMeansIrreducibleRepresentations = false
    ; sevenMeansIrreducibleRepresentationsIsFalse = refl
    }
