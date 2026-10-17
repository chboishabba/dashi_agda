{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440UniformTargetExact where

------------------------------------------------------------------------
-- CANONICAL B4 / EXACT UNIFORM PHYSICAL R440 OPEN LEMMA
--
-- The source-facing B4 programme has already reduced the critical-touching
-- term to one literal physical defect payment.  The principal Core-Core term
-- is paid at exactly one half of the literal companion, so the only remaining
-- strict-margin theorem is the uniform defect estimate
--
--   signedWork(u,N,k)
--     <= thetaD * coreMass(u,N,k) + cD * localED(u,N,k)
--
-- for every physical state u and retained output k at every cutoff N, with
--
--   0 <= thetaD < 1/2,
--   0 <= cD,
--   0 <= coreMass(u,N,k),
--   0 <= localED(u,N,k).
--
-- thetaD and cD are PARAMETERS OF THE WHOLE FAMILY, not functions of state,
-- cutoff, or output.  This is the exact cutoff/state/output uniformity needed
-- by the downstream strict-split compiler.
--
-- All three observables also carry explicit same-source attachment predicates.
-- Hence no producer can satisfy the target by choosing unrelated scalars.
--
-- This module STATES the irreducible analytic AST.  It proves no R440
-- estimate and deliberately leaves the terminal closure flag false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; _<_)

oneHalf : ℚ
oneHalf = Int.+ 1 / 2

------------------------------------------------------------------------
-- Exact typed AST.
------------------------------------------------------------------------

record CanonicalB4PhysicalR440UniformTarget
    (SelectedPeriodicSource PhysicalState Cutoff Output : Set)
    (selectedSource : SelectedPeriodicSource)
    (IsPhysicalState : SelectedPeriodicSource → PhysicalState → Set)
    (RetainedOutput : SelectedPeriodicSource → Cutoff → Output → Set)
    (signedWork coreMass localED : PhysicalState → Cutoff → Output → ℚ)
    (SignedWorkBelongsToSource :
      SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set)
    (CoreMassBelongsToSource :
      SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set)
    (LocalEDBelongsToSource :
      SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set)
    (thetaD cD : ℚ) : Set₁ where
  field
    ----------------------------------------------------------------------
    -- GLOBAL CONSTANT INVARIANTS.
    ----------------------------------------------------------------------

    thetaDNonnegative :
      0ℚ ≤ thetaD

    thetaDStrictlyBelowHalf :
      thetaD < oneHalf

    defectEDCoefficientNonnegative :
      0ℚ ≤ cD

    ----------------------------------------------------------------------
    -- SAME-SOURCE / POSITIVITY INVARIANTS AT EVERY PHYSICAL INSTANCE.
    ----------------------------------------------------------------------

    signedWorkSourceAttachment :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      SignedWorkBelongsToSource
        selectedSource state cutoff output (signedWork state cutoff output)

    coreMassSourceAttachment :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      CoreMassBelongsToSource
        selectedSource state cutoff output (coreMass state cutoff output)

    localEDSourceAttachment :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      LocalEDBelongsToSource
        selectedSource state cutoff output (localED state cutoff output)

    coreMassNonnegative :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      0ℚ ≤ coreMass state cutoff output

    localEDNonnegative :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      0ℚ ≤ localED state cutoff output

    ----------------------------------------------------------------------
    -- KEY OPEN LEMMA.
    --
    -- Because thetaD and cD occur outside the quantified state/cutoff/output
    -- variables, inhabiting this field is exactly the desired uniform theorem.
    ----------------------------------------------------------------------

    uniformPhysicalR440DefectPayment :
      (state : PhysicalState) →
      (cutoff : Cutoff) →
      (output : Output) →
      IsPhysicalState selectedSource state →
      RetainedOutput selectedSource cutoff output →
      signedWork state cutoff output
      ≤ thetaD * coreMass state cutoff output
        + cD * localED state cutoff output

------------------------------------------------------------------------
-- Public theorem-name alias: this is the exact proposition still to inhabit.
------------------------------------------------------------------------

B4PhysicalR440KeyOpenLemma :
  (SelectedPeriodicSource PhysicalState Cutoff Output : Set) →
  (selectedSource : SelectedPeriodicSource) →
  (IsPhysicalState : SelectedPeriodicSource → PhysicalState → Set) →
  (RetainedOutput : SelectedPeriodicSource → Cutoff → Output → Set) →
  (signedWork coreMass localED : PhysicalState → Cutoff → Output → ℚ) →
  (SignedWorkBelongsToSource :
    SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set) →
  (CoreMassBelongsToSource :
    SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set) →
  (LocalEDBelongsToSource :
    SelectedPeriodicSource → PhysicalState → Cutoff → Output → ℚ → Set) →
  (thetaD cD : ℚ) → Set₁
B4PhysicalR440KeyOpenLemma = CanonicalB4PhysicalR440UniformTarget

------------------------------------------------------------------------
-- Status / explicit invariant ledger.
------------------------------------------------------------------------

b4UniformTargetUsesLiteralRationals : Bool
b4UniformTargetUsesLiteralRationals = true

b4UniformThetaAndCoefficientAreStateCutoffOutputIndependent : Bool
b4UniformThetaAndCoefficientAreStateCutoffOutputIndependent = true

b4UniformTargetRequiresThetaInHalfOpenInterval : Bool
b4UniformTargetRequiresThetaInHalfOpenInterval = true

b4UniformTargetRequiresNonnegativeEDCoefficient : Bool
b4UniformTargetRequiresNonnegativeEDCoefficient = true

b4UniformTargetRequiresCoreMassNonnegative : Bool
b4UniformTargetRequiresCoreMassNonnegative = true

b4UniformTargetRequiresLocalEDNonnegative : Bool
b4UniformTargetRequiresLocalEDNonnegative = true

b4UniformTargetRequiresSameSourceAttachments : Bool
b4UniformTargetRequiresSameSourceAttachments = true

b4UniformPhysicalR440PaymentClosed : Bool
b4UniformPhysicalR440PaymentClosed = false

clayPromotion : Bool
clayPromotion = false

b4UniformTargetUsesLiteralRationalsIsTrue :
  b4UniformTargetUsesLiteralRationals ≡ true
b4UniformTargetUsesLiteralRationalsIsTrue = refl

b4UniformThetaAndCoefficientAreStateCutoffOutputIndependentIsTrue :
  b4UniformThetaAndCoefficientAreStateCutoffOutputIndependent ≡ true
b4UniformThetaAndCoefficientAreStateCutoffOutputIndependentIsTrue = refl

b4UniformTargetRequiresThetaInHalfOpenIntervalIsTrue :
  b4UniformTargetRequiresThetaInHalfOpenInterval ≡ true
b4UniformTargetRequiresThetaInHalfOpenIntervalIsTrue = refl

b4UniformTargetRequiresNonnegativeEDCoefficientIsTrue :
  b4UniformTargetRequiresNonnegativeEDCoefficient ≡ true
b4UniformTargetRequiresNonnegativeEDCoefficientIsTrue = refl

b4UniformTargetRequiresCoreMassNonnegativeIsTrue :
  b4UniformTargetRequiresCoreMassNonnegative ≡ true
b4UniformTargetRequiresCoreMassNonnegativeIsTrue = refl

b4UniformTargetRequiresLocalEDNonnegativeIsTrue :
  b4UniformTargetRequiresLocalEDNonnegative ≡ true
b4UniformTargetRequiresLocalEDNonnegativeIsTrue = refl

b4UniformTargetRequiresSameSourceAttachmentsIsTrue :
  b4UniformTargetRequiresSameSourceAttachments ≡ true
b4UniformTargetRequiresSameSourceAttachmentsIsTrue = refl

b4UniformPhysicalR440PaymentClosedIsFalse :
  b4UniformPhysicalR440PaymentClosed ≡ false
b4UniformPhysicalR440PaymentClosedIsFalse = refl
