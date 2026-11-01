{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SwapInvariantFourClassScalarRound764Exact where

------------------------------------------------------------------------
-- ROUND764 / GENERIC SWAP-INVARIANT SCALAR CARRIER HAS EQUAL LH/HL SUMS
--
-- R130 proves that the authoritative physical Bony tag is the computed
-- Round25 dyadic class and transports under physical p/q swap as
--
--   LH <-> HL,    HH <-> HH,    CC <-> CC.
--
-- For any rational scalar cell v on physical incidences define zero-valued
-- class selectors.  If
--
--   v(swap beta) = v(beta),
--
-- then on the complete duplicate-free physical cutoff enumeration:
--
--   sum_LH v = sum_HL v.
--
-- The proof uses only:
--   * R130 tag equivariance,
--   * R38 swap permutation of the complete enumeration,
--   * finite scalar addition.
--
-- No positivity, absolute value, norm, division, or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact as R130

lowHighPart :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
lowHighPart value tau with Bony.bonyTag tau
... | Bony.lhTag = value tau
... | Bony.hlTag = 0ℚ
... | Bony.hhToLowTag = 0ℚ
... | Bony.comparableTag = 0ℚ

highLowPart :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
highLowPart value tau with Bony.bonyTag tau
... | Bony.lhTag = 0ℚ
... | Bony.hlTag = value tau
... | Bony.hhToLowTag = 0ℚ
... | Bony.comparableTag = 0ℚ

highHighPart :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
highHighPart value tau with Bony.bonyTag tau
... | Bony.lhTag = 0ℚ
... | Bony.hlTag = 0ℚ
... | Bony.hhToLowTag = value tau
... | Bony.comparableTag = 0ℚ

comparablePart :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
comparablePart value tau with Bony.bonyTag tau
... | Bony.lhTag = 0ℚ
... | Bony.hlTag = 0ℚ
... | Bony.hhToLowTag = 0ℚ
... | Bony.comparableTag = value tau

pointwiseFourClassPartition :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  value tau
  ≡
  lowHighPart value tau
    + highLowPart value tau
    + comparablePart value tau
    + highHighPart value tau
pointwiseFourClassPartition value tau with Bony.bonyTag tau
... | Bony.lhTag = solve (value tau ∷ [])
... | Bony.hlTag = solve (value tau ∷ [])
... | Bony.hhToLowTag = solve (value tau ∷ [])
... | Bony.comparableTag = solve (value tau ∷ [])

foldPointwise :
  (left right : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  R38.foldPower left items ≡ R38.foldPower right items
foldPointwise left right pointwise [] = refl
foldPointwise left right pointwise (tau ∷ rest) =
  cong₂ _+_
    (pointwise tau)
    (foldPointwise left right pointwise rest)

foldFourClassPartition :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  R38.foldPower value items
  ≡
  R38.foldPower (lowHighPart value) items
    + R38.foldPower (highLowPart value) items
    + R38.foldPower (comparablePart value) items
    + R38.foldPower (highHighPart value) items
foldFourClassPartition value [] = solve []
foldFourClassPartition value (tau ∷ rest) =
  let
    v = value tau
    lh = lowHighPart value tau
    hl = highLowPart value tau
    cc = comparablePart value tau
    hh = highHighPart value tau

    V = R38.foldPower value rest
    LH = R38.foldPower (lowHighPart value) rest
    HL = R38.foldPower (highLowPart value) rest
    CC = R38.foldPower (comparablePart value) rest
    HH = R38.foldPower (highHighPart value) rest
  in
  trans
    (cong (v +_) (foldFourClassPartition value rest))
    (trans
      (cong
        (λ head →
          head + (LH + HL + CC + HH))
        (pointwiseFourClassPartition value tau))
      (solve (lh ∷ hl ∷ cc ∷ hh ∷ LH ∷ HL ∷ CC ∷ HH ∷ [])))

lowHighAfterSwapIsHighLow :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) →
    value (Symmetry.swapTriad tau) ≡ value tau) →
  (tau : Physical.PhysicalTriadIncidence) →
  lowHighPart value (Symmetry.swapTriad tau)
  ≡ highLowPart value tau
lowHighAfterSwapIsHighLow value invariant tau
  rewrite R130.bonyTagSwapEquivariant tau
        | invariant tau
  with Bony.bonyTag tau
... | Bony.lhTag = refl
... | Bony.hlTag = refl
... | Bony.hhToLowTag = refl
... | Bony.comparableTag = refl

highLowAfterSwapIsLowHigh :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) →
    value (Symmetry.swapTriad tau) ≡ value tau) →
  (tau : Physical.PhysicalTriadIncidence) →
  highLowPart value (Symmetry.swapTriad tau)
  ≡ lowHighPart value tau
highLowAfterSwapIsLowHigh value invariant tau
  rewrite R130.bonyTagSwapEquivariant tau
        | invariant tau
  with Bony.bonyTag tau
... | Bony.lhTag = refl
... | Bony.hlTag = refl
... | Bony.hhToLowTag = refl
... | Bony.comparableTag = refl

foldAfterSwapIsOriginal :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (cutoff : Nat) →
  R38.foldPower
    (λ tau → value (Symmetry.swapTriad tau))
    (Physical.physicalTriadEnumeration cutoff)
  ≡
  R38.foldPower value
    (Physical.physicalTriadEnumeration cutoff)
foldAfterSwapIsOriginal value cutoff =
  trans
    (sym
      (R38.foldMap
        value Symmetry.swapTriad
        (Physical.physicalTriadEnumeration cutoff)))
    (R38.foldPermutationInvariant
      value (R38.swapTriadEnumerationPermutation cutoff))

completeLowHighEqualsHighLow :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) →
    value (Symmetry.swapTriad tau) ≡ value tau) →
  (cutoff : Nat) →
  R38.foldPower
    (lowHighPart value)
    (Physical.physicalTriadEnumeration cutoff)
  ≡
  R38.foldPower
    (highLowPart value)
    (Physical.physicalTriadEnumeration cutoff)
completeLowHighEqualsHighLow value invariant cutoff =
  let
    items = Physical.physicalTriadEnumeration cutoff
  in
  trans
    (sym
      (foldAfterSwapIsOriginal (lowHighPart value) cutoff))
    (foldPointwise
      (λ tau → lowHighPart value (Symmetry.swapTriad tau))
      (highLowPart value)
      (lowHighAfterSwapIsHighLow value invariant)
      items)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round764AuthoritativeR25R130ClassSelectors : Bool
round764AuthoritativeR25R130ClassSelectors = true

round764GenericSwapInvariantLHHLExactEquality : Bool
round764GenericSwapInvariantLHHLExactEquality = true

round764NoProofCarryingClassifierPermutationNeeded : Bool
round764NoProofCarryingClassifierPermutationNeeded = true

round764IntroducesEstimate : Bool
round764IntroducesEstimate = false

round764IntroducesNormOrAbsoluteValue : Bool
round764IntroducesNormOrAbsoluteValue = false

round764ClayPromotion : Bool
round764ClayPromotion = false

round764AuthoritativeR25R130ClassSelectorsIsTrue :
  round764AuthoritativeR25R130ClassSelectors ≡ true
round764AuthoritativeR25R130ClassSelectorsIsTrue = refl

round764GenericSwapInvariantLHHLExactEqualityIsTrue :
  round764GenericSwapInvariantLHHLExactEquality ≡ true
round764GenericSwapInvariantLHHLExactEqualityIsTrue = refl

round764NoProofCarryingClassifierPermutationNeededIsTrue :
  round764NoProofCarryingClassifierPermutationNeeded ≡ true
round764NoProofCarryingClassifierPermutationNeededIsTrue = refl

round764IntroducesEstimateIsFalse :
  round764IntroducesEstimate ≡ false
round764IntroducesEstimateIsFalse = refl

round764IntroducesNormOrAbsoluteValueIsFalse :
  round764IntroducesNormOrAbsoluteValue ≡ false
round764IntroducesNormOrAbsoluteValueIsFalse = refl

round764ClayPromotionIsFalse :
  round764ClayPromotion ≡ false
round764ClayPromotionIsFalse = refl
