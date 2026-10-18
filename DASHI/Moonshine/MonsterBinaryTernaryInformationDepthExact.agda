module DASHI.Moonshine.MonsterBinaryTernaryInformationDepthExact where

------------------------------------------------------------------------
-- MONSTER BINARY / TERNARY INFORMATION DEPTH
--
-- Attribution:
--   JMD prompted the comparison 2^179 <= |M| < 3^113 and the numerical
--   spread between those two radix capacities.
--
-- Interpretation discipline:
--   180 bits and 113 trits are fixed-width coding depths for the cardinality
--   of the Monster group.  They are not promoted to new Monster-group
--   invariants or representation dimensions.
--
-- Strict inequalities are represented constructively by nonzero gap
-- equalities.  This avoids hiding the proof inside floating-point logarithms.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_^_)

------------------------------------------------------------------------
-- 1. Exact Monster order.
------------------------------------------------------------------------

monsterOrderExact : Nat
monsterOrderExact =
  808017424794512875886459904961710757005754368000000000

monsterOrderPrimeFactorization :
  monsterOrderExact
  ≡ (2 ^ 46)
    * (3 ^ 20)
    * (5 ^ 9)
    * (7 ^ 6)
    * (11 ^ 2)
    * (13 ^ 3)
    * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71
monsterOrderPrimeFactorization = refl

------------------------------------------------------------------------
-- 2. Exact radix capacities.
------------------------------------------------------------------------

twoPow179 : Nat
twoPow179 =
  766247770432944429179173513575154591809369561091801088

twoPow180 : Nat
twoPow180 =
  1532495540865888858358347027150309183618739122183602176

threePow112 : Nat
threePow112 =
  273892744995340833777347939263771534786080723599733441

threePow113 : Nat
threePow113 =
  821678234986022501332043817791314604358242170799200323

twoPow179IsPower : twoPow179 ≡ 2 ^ 179
twoPow179IsPower = refl

twoPow180IsPower : twoPow180 ≡ 2 ^ 180
twoPow180IsPower = refl

threePow112IsPower : threePow112 ≡ 3 ^ 112
threePow112IsPower = refl

threePow113IsPower : threePow113 ≡ 3 ^ 113
threePow113IsPower = refl

------------------------------------------------------------------------
-- 3. Constructive strict-bound witnesses.
------------------------------------------------------------------------

binaryLowerGap : Nat
binaryLowerGap =
  41769654361568446707286391386556165196384806908198912

binaryUpperGap : Nat
binaryUpperGap =
  724478116071375982471887122188598426612984754183602176

ternaryLowerGap : Nat
ternaryLowerGap =
  534124679799172042109111965697939222219673644400266559

ternaryUpperGap : Nat
ternaryUpperGap =
  13660810191509625445583912829603847352487802799200323

twoPow179BelowMonster :
  monsterOrderExact ≡ twoPow179 + binaryLowerGap
twoPow179BelowMonster = refl

monsterBelowTwoPow180 :
  twoPow180 ≡ monsterOrderExact + binaryUpperGap
monsterBelowTwoPow180 = refl

threePow112BelowMonster :
  monsterOrderExact ≡ threePow112 + ternaryLowerGap
threePow112BelowMonster = refl

monsterBelowThreePow113 :
  threePow113 ≡ monsterOrderExact + ternaryUpperGap
monsterBelowThreePow113 = refl

binaryLowerGapPositive :
  binaryLowerGap
  ≡ suc 41769654361568446707286391386556165196384806908198911
binaryLowerGapPositive = refl

binaryUpperGapPositive :
  binaryUpperGap
  ≡ suc 724478116071375982471887122188598426612984754183602175
binaryUpperGapPositive = refl

ternaryLowerGapPositive :
  ternaryLowerGap
  ≡ suc 534124679799172042109111965697939222219673644400266558
ternaryLowerGapPositive = refl

ternaryUpperGapPositive :
  ternaryUpperGap
  ≡ suc 13660810191509625445583912829603847352487802799200322
ternaryUpperGapPositive = refl

------------------------------------------------------------------------
-- 4. Typed fixed-width depth receipts.
------------------------------------------------------------------------

record RadixDepthReceipt : Set where
  constructor radix-depth-receipt
  field
    radix : Nat
    lowerExponent : Nat
    upperExponent : Nat
    lowerCapacity : Nat
    upperCapacity : Nat
    lowerGap : Nat
    upperGap : Nat
    lowerCapacityIsPower : lowerCapacity ≡ radix ^ lowerExponent
    upperCapacityIsPower : upperCapacity ≡ radix ^ upperExponent
    orderIsLowerPlusPositiveGap : monsterOrderExact ≡ lowerCapacity + lowerGap
    upperIsOrderPlusPositiveGap : upperCapacity ≡ monsterOrderExact + upperGap

open RadixDepthReceipt public

monsterBinaryDepthReceipt : RadixDepthReceipt
monsterBinaryDepthReceipt =
  radix-depth-receipt
    2 179 180
    twoPow179 twoPow180
    binaryLowerGap binaryUpperGap
    twoPow179IsPower
    twoPow180IsPower
    twoPow179BelowMonster
    monsterBelowTwoPow180

monsterTernaryDepthReceipt : RadixDepthReceipt
monsterTernaryDepthReceipt =
  radix-depth-receipt
    3 112 113
    threePow112 threePow113
    ternaryLowerGap ternaryUpperGap
    threePow112IsPower
    threePow113IsPower
    threePow112BelowMonster
    monsterBelowThreePow113

monsterBitDepthIs180 :
  upperExponent monsterBinaryDepthReceipt ≡ 180
monsterBitDepthIs180 = refl

monsterTritDepthIs113 :
  upperExponent monsterTernaryDepthReceipt ≡ 113
monsterTritDepthIs113 = refl

largestInsufficientBinaryExponentIs179 :
  lowerExponent monsterBinaryDepthReceipt ≡ 179
largestInsufficientBinaryExponentIs179 = refl

largestInsufficientTernaryExponentIs112 :
  lowerExponent monsterTernaryDepthReceipt ≡ 112
largestInsufficientTernaryExponentIs112 = refl

------------------------------------------------------------------------
-- 5. JMD quoted spread, exactly and without decimal approximation.
------------------------------------------------------------------------

jmdSpread : Nat
jmdSpread =
  55430464553078072152870304216160012548872609707399235

jmdSpreadExact :
  threePow113 ≡ twoPow179 + jmdSpread
jmdSpreadExact = refl

------------------------------------------------------------------------
-- 6. Semantic boundary.
------------------------------------------------------------------------

record MonsterInformationDepthBoundary : Set where
  constructor monster-information-depth-boundary
  field
    jmdRadixComparisonCredited : Bool
    exactMonsterOrderPaid : Bool
    binaryStrictBracketPaid : Bool
    ternaryStrictBracketPaid : Bool
    fixedWidthBitDepthPaid : Bool
    fixedWidthTritDepthPaid : Bool
    exactJMDSpreadPaid : Bool
    bitDepthIsNewMonsterRepresentationInvariant : Bool
    tritDepthIsNewMonsterRepresentationInvariant : Bool

canonicalMonsterInformationDepthBoundary :
  MonsterInformationDepthBoundary
canonicalMonsterInformationDepthBoundary =
  monster-information-depth-boundary
    true true true true true true true false false
