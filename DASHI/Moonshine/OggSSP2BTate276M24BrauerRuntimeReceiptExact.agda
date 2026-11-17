module DASHI.Moonshine.OggSSP2BTate276M24BrauerRuntimeReceiptExact where

------------------------------------------------------------------------
-- EXECUTED 2B TATE-276 / M24 DUAD BRAUER-CHARACTER RECEIPT
--
-- Provenance: DASHI CTblLib runtime computation executed after PR #1053.
-- Every 2-regular M24 class matched the genuine degree-276 duad character;
-- compatible lifts through the 2B-centralizer fusion chain gave independent
-- traces.  This pays the semisimplified/Jordan-Hoelder ingress after the
-- standard Brauer-character uniqueness theorem, but does NOT construct a
-- canonical literal Tate<->duad module isomorphism or an explicit Q10 chain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

record TwoRegularRow : Set where
  constructor two-regular-row
  field
    m24Class : Nat
    elementOrder : Nat
    co1Class : Nat
    tateTrace : Nat
    duadTrace : Nat
    compatibleLiftCount : Nat

open TwoRegularRow public

row1 : TwoRegularRow
row1 = two-regular-row 1 1 1 276 276 1
row4 : TwoRegularRow
row4 = two-regular-row 4 3 6 15 15 1
row5 : TwoRegularRow
row5 = two-regular-row 5 3 8 0 0 1
row9 : TwoRegularRow
row9 = two-regular-row 9 5 16 6 6 1
row12 : TwoRegularRow
row12 = two-regular-row 12 7 28 3 3 1
row13 : TwoRegularRow
row13 = two-regular-row 13 7 28 3 3 1
row16 : TwoRegularRow
row16 = two-regular-row 16 11 44 1 1 1
row21 : TwoRegularRow
row21 = two-regular-row 21 15 64 0 0 1
row22 : TwoRegularRow
row22 = two-regular-row 22 15 64 0 0 1
row23 : TwoRegularRow
row23 = two-regular-row 23 21 76 0 0 1
row24 : TwoRegularRow
row24 = two-regular-row 24 21 76 0 0 1
row25 : TwoRegularRow
row25 = two-regular-row 25 23 78 0 0 1
row26 : TwoRegularRow
row26 = two-regular-row 26 23 79 0 0 1

row1Matches : tateTrace row1 ≡ duadTrace row1
row1Matches = refl
row4Matches : tateTrace row4 ≡ duadTrace row4
row4Matches = refl
row5Matches : tateTrace row5 ≡ duadTrace row5
row5Matches = refl
row9Matches : tateTrace row9 ≡ duadTrace row9
row9Matches = refl
row12Matches : tateTrace row12 ≡ duadTrace row12
row12Matches = refl
row13Matches : tateTrace row13 ≡ duadTrace row13
row13Matches = refl
row16Matches : tateTrace row16 ≡ duadTrace row16
row16Matches = refl
row21Matches : tateTrace row21 ≡ duadTrace row21
row21Matches = refl
row22Matches : tateTrace row22 ≡ duadTrace row22
row22Matches = refl
row23Matches : tateTrace row23 ≡ duadTrace row23
row23Matches = refl
row24Matches : tateTrace row24 ≡ duadTrace row24
row24Matches = refl
row25Matches : tateTrace row25 ≡ duadTrace row25
row25Matches = refl
row26Matches : tateTrace row26 ≡ duadTrace row26
row26Matches = refl

record Tate276M24BrauerRuntimeReceipt : Set where
  constructor tate276-m24-brauer-runtime-receipt
  field
    twoRegularClassCount : Nat
    allLiftTracesIndependent : Bool
    allBrauerRowsMatch : Bool
    actualWeightTwoTateTraceUsed : Bool
    genuineM24DuadCharacterUsed : Bool
    semisimplifiedIngressPaid : Bool
    literalTateDuadIsomorphismPaid : Bool
    explicitActualQ10SubquotientPaid : Bool
    source : String

open Tate276M24BrauerRuntimeReceipt public

canonicalTate276M24BrauerRuntimeReceipt : Tate276M24BrauerRuntimeReceipt
canonicalTate276M24BrauerRuntimeReceipt =
  tate276-m24-brauer-runtime-receipt
    13 true true true true true false false
    "DASHI CTblLib runtime: all 13 2-regular M24 classes match Tate-276 vs duad-276"

classCountIsThirteen :
  twoRegularClassCount canonicalTate276M24BrauerRuntimeReceipt ≡ 13
classCountIsThirteen = refl

allLiftTracesIndependentIsTrue :
  allLiftTracesIndependent canonicalTate276M24BrauerRuntimeReceipt ≡ true
allLiftTracesIndependentIsTrue = refl

allBrauerRowsMatchIsTrue :
  allBrauerRowsMatch canonicalTate276M24BrauerRuntimeReceipt ≡ true
allBrauerRowsMatchIsTrue = refl

semisimplifiedIngressIsPaid :
  semisimplifiedIngressPaid canonicalTate276M24BrauerRuntimeReceipt ≡ true
semisimplifiedIngressIsPaid = refl

literalModuleIsomorphismStillOpen :
  literalTateDuadIsomorphismPaid canonicalTate276M24BrauerRuntimeReceipt ≡ false
literalModuleIsomorphismStillOpen = refl

explicitQ10StillOpen :
  explicitActualQ10SubquotientPaid canonicalTate276M24BrauerRuntimeReceipt ≡ false
explicitQ10StillOpen = refl
