module DASHI.Biology.TernaryMonsterSymmetryCandidateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced

------------------------------------------------------------------------
-- Exact arithmetic and typed symmetry sectors behind the proposed
--
--   196884 = 10 * 3^9 + 54,
--   196883 = 10 * 3^9 + (54 - 1)
--
-- construction.  The arithmetic and reduced-fibre source of 53 are proved.
-- A restriction/decomposition of the Monster representation is deliberately
-- retained as an open candidate.

data D4IrrepKind : Set where
  A1 : D4IrrepKind
  A2 : D4IrrepKind
  B1 : D4IrrepKind
  B2 : D4IrrepKind
  E2 : D4IrrepKind

irrepDimension : D4IrrepKind → Nat
irrepDimension A1 = 1
irrepDimension A2 = 1
irrepDimension B1 = 1
irrepDimension B2 = 1
irrepDimension E2 = 2

------------------------------------------------------------------------
-- Raw permutation representation of D4 on the nine cells:
--
--   R^9 = 3 A1 + B1 + B2 + 2 E.
--
-- The reflection-odd A2 species is absent from the bare cell permutation
-- representation and requires an orientation/pseudoscalar/braid refinement.

rawNineMultiplicity : D4IrrepKind → Nat
rawNineMultiplicity A1 = 3
rawNineMultiplicity A2 = 0
rawNineMultiplicity B1 = 1
rawNineMultiplicity B2 = 1
rawNineMultiplicity E2 = 2

rawContribution : D4IrrepKind → Nat
rawContribution kind =
  rawNineMultiplicity kind * irrepDimension kind

rawNineRepresentationDimension : Nat
rawNineRepresentationDimension =
  rawContribution A1
  + rawContribution A2
  + rawContribution B1
  + rawContribution B2
  + rawContribution E2

rawNineRepresentationDimensionIsNine :
  rawNineRepresentationDimension ≡ 9
rawNineRepresentationDimensionIsNine = refl

rawA2MultiplicityIsZero : rawNineMultiplicity A2 ≡ 0
rawA2MultiplicityIsZero = refl

data DialecticalOrientation : Set where
  positiveOrientation : DialecticalOrientation
  negativeOrientation : DialecticalOrientation

record SymmetrySector : Set where
  constructor symmetrySector
  field
    irrepKind : D4IrrepKind
    orientation : DialecticalOrientation

open SymmetrySector public

canonicalTenSectors : List SymmetrySector
canonicalTenSectors =
  symmetrySector A1 positiveOrientation
  ∷ symmetrySector A1 negativeOrientation
  ∷ symmetrySector A2 positiveOrientation
  ∷ symmetrySector A2 negativeOrientation
  ∷ symmetrySector B1 positiveOrientation
  ∷ symmetrySector B1 negativeOrientation
  ∷ symmetrySector B2 positiveOrientation
  ∷ symmetrySector B2 negativeOrientation
  ∷ symmetrySector E2 positiveOrientation
  ∷ symmetrySector E2 negativeOrientation
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sectorCountIsTen : listCount canonicalTenSectors ≡ 10
sectorCountIsTen = refl

ternarySheetDimension : Nat
ternarySheetDimension = Hyper.ternaryLatticeCount 9

ternarySheetDimensionIs19683 : ternarySheetDimension ≡ 19683
ternarySheetDimensionIs19683 = refl

bulkDimension : Nat
bulkDimension = 10 * ternarySheetDimension

bulkDimensionIs196830 : bulkDimension ≡ 196830
bulkDimensionIs196830 = refl

fullSixByNineDimension : Nat
fullSixByNineDimension = Reduced.fullSixByNineDimension

fullSixByNineDimensionIs54 : fullSixByNineDimension ≡ 54
fullSixByNineDimensionIs54 = refl

residualDimension : Nat
residualDimension = Reduced.reducedDimension

residualDimensionIs53 : residualDimension ≡ 53
residualDimensionIs53 = refl

moonshineCoefficientCandidateDimension : Nat
moonshineCoefficientCandidateDimension = bulkDimension + fullSixByNineDimension

moonshineCoefficientCandidateDimensionIs196884 :
  moonshineCoefficientCandidateDimension ≡ 196884
moonshineCoefficientCandidateDimensionIs196884 = refl

monsterCandidateDimension : Nat
monsterCandidateDimension = bulkDimension + residualDimension

monsterCandidateDimensionIs196883 : monsterCandidateDimension ≡ 196883
monsterCandidateDimensionIs196883 = refl

coefficientSplitsAsInvariantPlusMonsterCandidate :
  1 + monsterCandidateDimension ≡ moonshineCoefficientCandidateDimension
coefficientSplitsAsInvariantPlusMonsterCandidate = refl

------------------------------------------------------------------------
-- Ogg-prime arithmetic.

canonicalOggPrimes : List Nat
canonicalOggPrimes =
  2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19
  ∷ 23 ∷ 29 ∷ 31 ∷ 41 ∷ 47 ∷ 59 ∷ 71 ∷ []

canonicalOggPrimeCountIsFifteen : listCount canonicalOggPrimes ≡ 15
canonicalOggPrimeCountIsFifteen = refl

isOggPrime : Nat → Bool
isOggPrime 2 = true
isOggPrime 3 = true
isOggPrime 5 = true
isOggPrime 7 = true
isOggPrime 11 = true
isOggPrime 13 = true
isOggPrime 17 = true
isOggPrime 19 = true
isOggPrime 23 = true
isOggPrime 29 = true
isOggPrime 31 = true
isOggPrime 41 = true
isOggPrime 47 = true
isOggPrime 59 = true
isOggPrime 71 = true
isOggPrime n = false

largestThreeOggPrimesMultiplyTo196883 : 47 * 59 * 71 ≡ 196883
largestThreeOggPrimesMultiplyTo196883 = refl

fortySevenIsOggPrime : isOggPrime 47 ≡ true
fortySevenIsOggPrime = refl

fiftyNineIsOggPrime : isOggPrime 59 ≡ true
fiftyNineIsOggPrime = refl

seventyOneIsOggPrime : isOggPrime 71 ≡ true
seventyOneIsOggPrime = refl

fiftyThreeIsNotAnOggPrime : isOggPrime 53 ≡ false
fiftyThreeIsNotAnOggPrime = refl

------------------------------------------------------------------------
-- Finite trial-division data for 53.  This records the only prime candidates
-- not exceeding sqrt(53); the module does not equate prime cardinality with an
-- irreducible representation.

record FiftyThreeTrialDivisionData : Set where
  constructor fiftyThreeTrialDivisionData
  field
    afterTwo : 2 * 26 + 1 ≡ 53
    afterThree : 3 * 17 + 2 ≡ 53
    afterFive : 5 * 10 + 3 ≡ 53
    afterSeven : 7 * 7 + 4 ≡ 53
    sevenSquared : 7 * 7 ≡ 49
    eightSquared : 8 * 8 ≡ 64

open FiftyThreeTrialDivisionData public

canonicalFiftyThreeTrialDivisionData : FiftyThreeTrialDivisionData
canonicalFiftyThreeTrialDivisionData =
  fiftyThreeTrialDivisionData refl refl refl refl refl refl

------------------------------------------------------------------------
-- Candidate restriction shape.  Dimensions alone do not construct module
-- actions, intertwining maps, invariant forms, or irreducibility.

record MonsterRestrictionCandidate : Set where
  constructor monsterRestrictionCandidate
  field
    fullTernaryFibres : Nat
    fibreDimension : Nat
    exceptionalResidualDimension : Nat
    totalDimension : Nat
    totalDimensionCertificate :
      fullTernaryFibres * fibreDimension + exceptionalResidualDimension
      ≡ totalDimension

open MonsterRestrictionCandidate public

canonicalMonsterRestrictionCandidate : MonsterRestrictionCandidate
canonicalMonsterRestrictionCandidate =
  monsterRestrictionCandidate 10 19683 53 196883 refl

canonicalReducedFiftyThreeBoundary : Reduced.ReducedFiftyThreeBoundary
canonicalReducedFiftyThreeBoundary =
  Reduced.canonicalReducedFiftyThreeBoundary

record MoonshinePromotionBoundary : Set where
  constructor moonshinePromotionBoundary
  field
    decimalIdentityIsMonsterRestrictionTheorem : Bool
    decimalIdentityIsMonsterRestrictionTheoremIsFalse :
      decimalIdentityIsMonsterRestrictionTheorem ≡ false

    fiftyThreeBeingPrimeWouldMakeItAnIrrep : Bool
    fiftyThreeBeingPrimeWouldMakeItAnIrrepIsFalse :
      fiftyThreeBeingPrimeWouldMakeItAnIrrep ≡ false

    tenCopiesAreAlreadyD4IsotypicComponents : Bool
    tenCopiesAreAlreadyD4IsotypicComponentsIsFalse :
      tenCopiesAreAlreadyD4IsotypicComponents ≡ false

    oggPrimeFactorisationSuppliesTheMissingAction : Bool
    oggPrimeFactorisationSuppliesTheMissingActionIsFalse :
      oggPrimeFactorisationSuppliesTheMissingAction ≡ false

    rawNineCellRepresentationContainsA2 : Bool
    rawNineCellRepresentationContainsA2IsFalse :
      rawNineCellRepresentationContainsA2 ≡ false

    gradedCharactersAndModularityRemainRequired : Bool
    gradedCharactersAndModularityRemainRequiredIsTrue :
      gradedCharactersAndModularityRemainRequired ≡ true

open MoonshinePromotionBoundary public

canonicalMoonshinePromotionBoundary : MoonshinePromotionBoundary
canonicalMoonshinePromotionBoundary =
  moonshinePromotionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
