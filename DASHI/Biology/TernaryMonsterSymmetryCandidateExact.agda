module DASHI.Biology.TernaryMonsterSymmetryCandidateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Exact arithmetic and typed symmetry sectors behind the proposed
--
--   196883 = 10 * 3^9 + 53
--
-- construction.  The arithmetic is proved.  A restriction/decomposition of
-- the Monster representation is deliberately retained as an open candidate.

data D4IrrepKind : Set where
  A1 : D4IrrepKind
  A2 : D4IrrepKind
  B1 : D4IrrepKind
  B2 : D4IrrepKind
  E2 : D4IrrepKind

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

residualDimension : Nat
residualDimension = 53

monsterCandidateDimension : Nat
monsterCandidateDimension = bulkDimension + residualDimension

monsterCandidateDimensionIs196883 : monsterCandidateDimension ≡ 196883
monsterCandidateDimensionIs196883 = refl

------------------------------------------------------------------------
-- Ogg-prime arithmetic.

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

    gradedCharactersAndModularityRemainRequired : Bool
    gradedCharactersAndModularityRemainRequiredIsTrue :
      gradedCharactersAndModularityRemainRequired ≡ true

open MoonshinePromotionBoundary public

canonicalMoonshinePromotionBoundary : MoonshinePromotionBoundary
canonicalMoonshinePromotionBoundary =
  moonshinePromotionBoundary false refl false refl false refl false refl true refl
