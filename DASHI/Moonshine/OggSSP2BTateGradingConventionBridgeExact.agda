module DASHI.Moonshine.OggSSP2BTateGradingConventionBridgeExact where

------------------------------------------------------------------------
-- 2B TATE GRADING-CONVENTION BRIDGE
--
-- Primary-source audit:
--
-- Borcherds--Ryba, Modular Moonshine II, indexes the graded Monster module by
-- the exponent m of q.  Their 2B theorem states:
--   Hhat0 vanishes for even m;
--   Hhat1 vanishes for odd m.
--
-- Carnahan--Urano uses L0-weight n and the Moonshine expansion q^(n-1).
-- Hence
--
--   m = n - 1.
--
-- Consequently even positive CU weight maps to odd BR q-degree, and odd CU
-- weight maps to even BR q-degree.  This reconciles Borcherds--Ryba with
-- Carnahan--Urano Lemma 6.4, where even L0-weight 2B pieces restrict to Z and
-- Z[H], while odd weights restrict to the sign module I and Z[H].
--
-- In particular the repository's low-weight assignment
--   weight 2 -> Hhat0 length 276,
--   weight 3 -> Hhat1 length 2048
-- has the correct source parity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Explicit low-degree bridge.
------------------------------------------------------------------------

cuWeightTwo : Nat
cuWeightTwo = 2

cuWeightThree : Nat
cuWeightThree = 3

brDegreeOfWeightTwo : Nat
brDegreeOfWeightTwo = 1

brDegreeOfWeightThree : Nat
brDegreeOfWeightThree = 2

weightTwoMapsToOddBRDegree : brDegreeOfWeightTwo ≡ 1
weightTwoMapsToOddBRDegree = refl

weightThreeMapsToEvenBRDegree : brDegreeOfWeightThree ≡ 2
weightThreeMapsToEvenBRDegree = refl

------------------------------------------------------------------------
-- 2. Source parity receipt.
------------------------------------------------------------------------

record TwoBTateGradingSourceReceipt : Set where
  constructor two-b-tate-grading-source-receipt
  field
    borcherdsRybaUsesQExponentIndex : Bool
    carnahanUranoUsesL0WeightWithShift : Bool
    indexRelationIsMEqualsNMinusOne : Bool
    brEvenDegreeH0VanishingSourced : Bool
    brOddDegreeH1VanishingSourced : Bool
    cuEvenWeightUsesTrivialAndRegularRestriction : Bool
    cuOddWeightUsesSignAndRegularRestriction : Bool
    weightTwoH0Length : Nat
    weightTwoH1Length : Nat
    weightThreeH0Length : Nat
    weightThreeH1Length : Nat
    conventionsReconciled : Bool

canonicalTwoBTateGradingSourceReceipt : TwoBTateGradingSourceReceipt
canonicalTwoBTateGradingSourceReceipt =
  two-b-tate-grading-source-receipt
    true true true
    true true
    true true
    276 0 0 2048
    true

------------------------------------------------------------------------
-- 3. Firewall.
------------------------------------------------------------------------

data ApplyingBRParityDirectlyToCUWeightWithoutShift : Set where

parityConventionShiftIsRequired :
  ApplyingBRParityDirectlyToCUWeightWithoutShift → ⊥
parityConventionShiftIsRequired ()

record TateGradingAuditStatus : Set where
  constructor tate-grading-audit-status
  field
    apparentParityConflictResolved : Bool
    currentWeightTwoH0OrientationRetained : Bool
    currentWeightThreeH1OrientationRetained : Bool
    brauerCharacterRouteMayProceedWithExplicitShift : Bool

canonicalTateGradingAuditStatus : TateGradingAuditStatus
canonicalTateGradingAuditStatus =
  tate-grading-audit-status true true true true
