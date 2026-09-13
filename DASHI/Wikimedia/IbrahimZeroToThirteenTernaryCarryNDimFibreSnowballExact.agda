module DASHI.Wikimedia.IbrahimZeroToThirteenTernaryCarryNDimFibreSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact as Rank
import DASHI.Wikimedia.IbrahimOneThreeSixOneNineTenBulkOEISSnowballExact as Bulk
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine

------------------------------------------------------------------------
-- 0..13 AS AN EXACT TERNARY PLACE-VALUE ATLAS
--
-- This is the missing clean owner for the user's "pure 1 / pure 2 / pure 3 /
-- combinations" intuition.  Every n=0..13 is written with ternary digits
-- (u,t,n) in the place values
--
--        1, 3, 9
--
-- so value = u + 3*t + 9*n, with each displayed digit in {0,1,2}.
--
-- In ordinary ternary notation this gives
--
--   0,1,2,10,11,12,20,21,22,100,101,102,110,111,
--
-- exactly the prefix of OEIS A007089 (numbers written in base 3).
--
-- The place-value identities explain the requested 1/3/6 and 1/9 views:
--
--   6 = 2*3,
--   7 = 1+6,
--   8 = 2+6,
--   9 = 9,
--   10 = 1+9 = 1+3+6,
--   12 = 3+9,
--   13 = 1+3+9.
--
-- The equality 3+6=9 is the carry weld between the two descriptions of 10.
------------------------------------------------------------------------

record Ternary013Row : Set where
  constructor ternary-013-row
  field
    rank : Rank.RankZeroToThirteen
    unitsDigit : Nat
    threesDigit : Nat
    ninesDigit : Nat
    renderedBase3 : String
    value : Nat
    valueMatchesRank : value ≡ Rank.rankToNat rank
    placeValuePaid : value ≡ unitsDigit + 3 * threesDigit + 9 * ninesDigit
open Ternary013Row public

r0  = ternary-013-row Rank.rank0  0 0 0 "0"   0  refl refl
r1  = ternary-013-row Rank.rank1  1 0 0 "1"   1  refl refl
r2  = ternary-013-row Rank.rank2  2 0 0 "2"   2  refl refl
r3  = ternary-013-row Rank.rank3  0 1 0 "10"  3  refl refl
r4  = ternary-013-row Rank.rank4  1 1 0 "11"  4  refl refl
r5  = ternary-013-row Rank.rank5  2 1 0 "12"  5  refl refl
r6  = ternary-013-row Rank.rank6  0 2 0 "20"  6  refl refl
r7  = ternary-013-row Rank.rank7  1 2 0 "21"  7  refl refl
r8  = ternary-013-row Rank.rank8  2 2 0 "22"  8  refl refl
r9  = ternary-013-row Rank.rank9  0 0 1 "100" 9  refl refl
r10 = ternary-013-row Rank.rank10 1 0 1 "101" 10 refl refl
r11 = ternary-013-row Rank.rank11 2 0 1 "102" 11 refl refl
r12 = ternary-013-row Rank.rank12 0 1 1 "110" 12 refl refl
r13 = ternary-013-row Rank.rank13 1 1 1 "111" 13 refl refl

canonicalZeroToThirteenTernaryRows : List Ternary013Row
canonicalZeroToThirteenTernaryRows =
  r0 ∷ r1 ∷ r2 ∷ r3 ∷ r4 ∷ r5 ∷ r6 ∷
  r7 ∷ r8 ∷ r9 ∷ r10 ∷ r11 ∷ r12 ∷ r13 ∷ []

------------------------------------------------------------------------
-- Carry identities / alternate block readings.
------------------------------------------------------------------------

sixAsTwoThrees : 6 ≡ 2 * 3
sixAsTwoThrees = refl

sevenAsOnePlusSix : 7 ≡ 1 + 6
sevenAsOnePlusSix = refl

eightAsTwoPlusSix : 8 ≡ 2 + 6
eightAsTwoPlusSix = refl

threePlusSixIsNine : 3 + 6 ≡ 9
threePlusSixIsNine = refl

tenAsOnePlusNine : 10 ≡ 1 + 9
tenAsOnePlusNine = refl

tenAsOnePlusThreePlusSix : 10 ≡ 1 + 3 + 6
tenAsOnePlusThreePlusSix = refl

oneThreeSixCarryMatchesOneNine : 1 + 3 + 6 ≡ 1 + 9
oneThreeSixCarryMatchesOneNine = refl

twelveAsThreePlusNine : 12 ≡ 3 + 9
twelveAsThreePlusNine = refl

thirteenAsOnePlusThreePlusNine : 13 ≡ 1 + 3 + 9
thirteenAsOnePlusThreePlusNine = refl

bulkTenSplitAgreement : Bulk.onePlusThreePlusSixIsTen ≡ Bulk.onePlusNineIsTen
bulkTenSplitAgreement = refl

------------------------------------------------------------------------
-- N-dimensional fibre interpretation.
--
-- IMPORTANT: the ternary digits describe the integer INDEX n.  The fixed
-- n-axis ternary fibre has 3^n states.  Those are separate coordinates.
------------------------------------------------------------------------

rank7Index : Rank.rankToNat Rank.rank7 ≡ 7
rank7Index = refl

rank7FixedTernaryProfiles : Rank.fixedTernaryProfileCount Rank.rank7 ≡ 2187
rank7FixedTernaryProfiles = refl

rank7ExternalE7DistinguishedCarrier :
  Rank.EnRankCoordinate.distinguishedFiniteCarrierDimension Rank.en7 ≡ 56
rank7ExternalE7DistinguishedCarrier = refl

rank9Index : Rank.rankToNat Rank.rank9 ≡ 9
rank9Index = refl

rank9FixedTernaryProfiles : Rank.fixedTernaryProfileCount Rank.rank9 ≡ 19683
rank9FixedTernaryProfiles = refl

rank9TenChannelBulk : Rank.tenChannelAt9 ≡ 196830
rank9TenChannelBulk = Rank.tenChannelAt9Is196830

rank13Index : Rank.rankToNat Rank.rank13 ≡ 13
rank13Index = refl

rank13FixedTernaryProfiles : Rank.fixedTernaryProfileCount Rank.rank13 ≡ 1594323
rank13FixedTernaryProfiles = refl

------------------------------------------------------------------------
-- OEIS / external coordinates.
------------------------------------------------------------------------

record ZeroToThirteenTernaryExternalCoordinates : Set where
  constructor zero-to-thirteen-ternary-external-coordinates
  field
    ternaryNumeralSystemQid : String
    base3RenderingOEIS : String
    powersOfThreeOEIS : String
    tenTimesPowersOfThreeOEIS : String
    a007089Prefix0to13Paid : Bool
    a000244FixedProfileFamilyPaid : Bool
    base3RenderingCreatesEnSemantics : Bool
    base3RenderingCreatesTetration : Bool
open ZeroToThirteenTernaryExternalCoordinates public

canonicalZeroToThirteenTernaryExternalCoordinates : ZeroToThirteenTernaryExternalCoordinates
canonicalZeroToThirteenTernaryExternalCoordinates =
  zero-to-thirteen-ternary-external-coordinates
    "Q1056486" "A007089" "A000244" "A005052"
    true true false false

------------------------------------------------------------------------
-- BIDI / WrongType boundaries.
------------------------------------------------------------------------

data TernaryDigitsCreateEnIdentity : Set where
data RankSevenCreatesFiftySixCarrier : Set where
data RankNineCreatesMonsterBulk : Set where
data BaseThreePrefixCreatesTetration : Set where
data OneThreeSixIdentityCreatesSameSemanticPartition : Set where

ternaryDigitsDoNotCreateEn : TernaryDigitsCreateEnIdentity → ⊥
ternaryDigitsDoNotCreateEn ()

sevenIndexDoesNotCreateE7Module : RankSevenCreatesFiftySixCarrier → ⊥
sevenIndexDoesNotCreateE7Module ()

nineIndexDoesNotCreateMonsterBulk : RankNineCreatesMonsterBulk → ⊥
nineIndexDoesNotCreateMonsterBulk ()

base3PrefixDoesNotCreateTetration : BaseThreePrefixCreatesTetration → ⊥
base3PrefixDoesNotCreateTetration ()

sameTenArithmeticDoesNotIdentifyPartitions : OneThreeSixIdentityCreatesSameSemanticPartition → ⊥
sameTenArithmeticDoesNotIdentifyPartitions ()

record ZeroToThirteenTernaryCarryBoundary : Set where
  constructor zero-to-thirteen-ternary-carry-boundary
  field
    exactTernaryRows0to13Paid : Bool
    a007089PrefixPaid : Bool
    oneThreeSixToOneNineCarryPaid : Bool
    rank7SeparatesIndex2187AndE7FiftySix : Bool
    rank9SeparatesIndex19683And196830Bulk : Bool
    rank13IsTernary111Paid : Bool
    fixedProfileCountsAreA000244Family : Bool
    theseRowsCreateSelfIndexedTetration : Bool
    theseRowsCreateExceptionalRepresentationIdentity : Bool
    nextResidual : String
open ZeroToThirteenTernaryCarryBoundary public

currentZeroToThirteenTernaryCarryBoundary : ZeroToThirteenTernaryCarryBoundary
currentZeroToThirteenTernaryCarryBoundary = zero-to-thirteen-ternary-carry-boundary
  true true true true true true true false false
  "use the exact 0..13 ternary digit atlas as a coordinate/index fibre: compare each index n with (a) its fixed ternary hyperfabric size 3^n, (b) its typed E_n/Lie-Kac-Moody coordinate where one exists, and (c) existing DASHI stage/consumer roles. The first high-value tests are n=6,7,8,9: 729/56/248/19683 already have strong but DIFFERENT external roles. Promote only when a same-carrier or FactorsThrough witness survives."
