module DASHI.Moonshine.MonsterOrderExponentCorrectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv: 2602.09135.
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Conway et al.,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN: 978-0-19-853199-9.
--
-- DASHI CONTRIBUTION
--
-- Install the exact Monster-order valuation table as the authoritative
-- fifteen-lane function, decompose the p > 3 values into the three modular
-- contributions of Duncan--Swisher Theorem 1.1, and expose a regression
-- witness for the older repository receipts that incorrectly assigned
-- exponent two to p = 13,17,19,23.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt as LegacyDepth
import DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface as LegacyValuation

monsterOrderExponent :
  Lane.MonsterPrimeLane →
  Nat
monsterOrderExponent Lane.p2 = 46
monsterOrderExponent Lane.p3 = 20
monsterOrderExponent Lane.p5 = 9
monsterOrderExponent Lane.p7 = 6
monsterOrderExponent Lane.p11 = 2
monsterOrderExponent Lane.p13 = 3
monsterOrderExponent Lane.p17 = 1
monsterOrderExponent Lane.p19 = 1
monsterOrderExponent Lane.p23 = 1
monsterOrderExponent Lane.p29 = 1
monsterOrderExponent Lane.p31 = 1
monsterOrderExponent Lane.p41 = 1
monsterOrderExponent Lane.p47 = 1
monsterOrderExponent Lane.p59 = 1
monsterOrderExponent Lane.p71 = 1

monsterOrderExponentVector15 : List Nat
monsterOrderExponentVector15 =
  46 ∷ 20 ∷ 9 ∷ 6 ∷ 2 ∷ 3
  ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

data PrimeAboveThree : Lane.MonsterPrimeLane → Set where
  p5AboveThree : PrimeAboveThree Lane.p5
  p7AboveThree : PrimeAboveThree Lane.p7
  p11AboveThree : PrimeAboveThree Lane.p11
  p13AboveThree : PrimeAboveThree Lane.p13
  p17AboveThree : PrimeAboveThree Lane.p17
  p19AboveThree : PrimeAboveThree Lane.p19
  p23AboveThree : PrimeAboveThree Lane.p23
  p29AboveThree : PrimeAboveThree Lane.p29
  p31AboveThree : PrimeAboveThree Lane.p31
  p41AboveThree : PrimeAboveThree Lane.p41
  p47AboveThree : PrimeAboveThree Lane.p47
  p59AboveThree : PrimeAboveThree Lane.p59
  p71AboveThree : PrimeAboveThree Lane.p71

record ModularValuationContribution
  (prime : Lane.MonsterPrimeLane) : Set where
  constructor modularValuationContribution
  field
    frickeLevel : Nat
    primeLevel : Nat
    squareLevel : Nat
    reconstructsExponent :
      frickeLevel + primeLevel + squareLevel
      ≡ monsterOrderExponent prime

open ModularValuationContribution public

modularContribution :
  (prime : Lane.MonsterPrimeLane) →
  PrimeAboveThree prime →
  ModularValuationContribution prime
modularContribution Lane.p5 p5AboveThree =
  modularValuationContribution 3 5 1 refl
modularContribution Lane.p7 p7AboveThree =
  modularValuationContribution 2 4 0 refl
modularContribution Lane.p11 p11AboveThree =
  modularValuationContribution 2 0 0 refl
modularContribution Lane.p13 p13AboveThree =
  modularValuationContribution 1 2 0 refl
modularContribution Lane.p17 p17AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p19 p19AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p23 p23AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p29 p29AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p31 p31AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p41 p41AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p47 p47AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p59 p59AboveThree =
  modularValuationContribution 1 0 0 refl
modularContribution Lane.p71 p71AboveThree =
  modularValuationContribution 1 0 0 refl

duncanSwisherExceptionalRHS :
  Lane.MonsterPrimeLane →
  Nat
duncanSwisherExceptionalRHS Lane.p2 = 36
duncanSwisherExceptionalRHS Lane.p3 = 18
duncanSwisherExceptionalRHS prime = monsterOrderExponent prime

p2ExceptionalGap :
  monsterOrderExponent Lane.p2
  ≡ duncanSwisherExceptionalRHS Lane.p2 + 10
p2ExceptionalGap = refl

p3ExceptionalGap :
  monsterOrderExponent Lane.p3
  ≡ duncanSwisherExceptionalRHS Lane.p3 + 2
p3ExceptionalGap = refl

p5ExponentIsNine : monsterOrderExponent Lane.p5 ≡ 9
p5ExponentIsNine = refl

p7ExponentIsSix : monsterOrderExponent Lane.p7 ≡ 6
p7ExponentIsSix = refl

p11ExponentIsTwo : monsterOrderExponent Lane.p11 ≡ 2
p11ExponentIsTwo = refl

p13ExponentIsThree : monsterOrderExponent Lane.p13 ≡ 3
p13ExponentIsThree = refl

legacyDepthP13WasTwo :
  LegacyDepth.monsterOrderDepthExponent Lane.p13 ≡ 2
legacyDepthP13WasTwo = refl

legacyValuationP13WasTwo :
  LegacyValuation.monsterOrderValuation Lane.p13 ≡ 2
legacyValuationP13WasTwo = refl

legacyDepthP13IsNotCorrect :
  ¬ (LegacyDepth.monsterOrderDepthExponent Lane.p13
     ≡ monsterOrderExponent Lane.p13)
legacyDepthP13IsNotCorrect ()

legacyValuationP13IsNotCorrect :
  ¬ (LegacyValuation.monsterOrderValuation Lane.p13
     ≡ monsterOrderExponent Lane.p13)
legacyValuationP13IsNotCorrect ()

legacyDepthP17IsNotCorrect :
  ¬ (LegacyDepth.monsterOrderDepthExponent Lane.p17
     ≡ monsterOrderExponent Lane.p17)
legacyDepthP17IsNotCorrect ()

legacyDepthP19IsNotCorrect :
  ¬ (LegacyDepth.monsterOrderDepthExponent Lane.p19
     ≡ monsterOrderExponent Lane.p19)
legacyDepthP19IsNotCorrect ()

legacyDepthP23IsNotCorrect :
  ¬ (LegacyDepth.monsterOrderDepthExponent Lane.p23
     ≡ monsterOrderExponent Lane.p23)
legacyDepthP23IsNotCorrect ()

record MonsterExponentBoundary : Set where
  constructor monsterExponentBoundary
  field
    theoremCoversTwoAndThree : Bool
    theoremCoversTwoAndThreeIsFalse :
      theoremCoversTwoAndThree ≡ false
    valuationIsRepresentationDimension : Bool
    valuationIsRepresentationDimensionIsFalse :
      valuationIsRepresentationDimension ≡ false
    fiveToNineExplainsD4Carrier : Bool
    fiveToNineExplainsD4CarrierIsFalse :
      fiveToNineExplainsD4Carrier ≡ false
    legacyReceiptIsAuthoritative : Bool
    legacyReceiptIsAuthoritativeIsFalse :
      legacyReceiptIsAuthoritative ≡ false

canonicalMonsterExponentBoundary : MonsterExponentBoundary
canonicalMonsterExponentBoundary =
  monsterExponentBoundary false refl false refl false refl false refl
