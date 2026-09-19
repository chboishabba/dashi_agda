module DASHI.Analysis.RiemannBishopSetoidCriticalLineRefinementExact where

------------------------------------------------------------------------
-- BISHOP SETOID EQUALITY TO 1/2 AS THE CONSTRUCTIVE CRITICAL-LINE REFINEMENT
--
-- Agda record equality is not the mathematical equality on Murray--Bishop
-- reals.  Use Bishop._≃_ instead.  Its definition is a family of rational <=
-- bounds, and each such bound is decidable.  Therefore Bishop real equality is
-- double-negation stable constructively, point by point.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Unnormalised as ℚ using (_≤_; _-_; ∣_∣; _/_)
import Data.Rational.Unnormalised.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_)

import Real as Bishop

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as RX
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as BishopHeight
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as BishopCarrier

halfRational : ℚ
halfRational = RX.half

bishopHalf : Bishop.ℝ
bishopHalf = BishopCarrier.bishopRationalEmbed halfRational

bishopEqualityBound :
  ∀ {left right : Bishop.ℝ} →
  Bishop._≃_ left right →
  (n : Nat) →
  {n≢0 : n ≢ 0} →
  ℚ.∣ Bishop.seq left n ℚ.- Bishop.seq right n ∣
  ℚ.≤
  (+ 2 / n)
bishopEqualityBound (Bishop.*≃* bounds) n = bounds n

bishopSetoidEqualityStable :
  (left right : Bishop.ℝ) →
  ((Bishop._≃_ left right → ⊥) → ⊥) →
  Bishop._≃_ left right
bishopSetoidEqualityStable left right nn =
  Bishop.*≃* bounds
  where
  bounds :
    (n : Nat) →
    {n≢0 : n ≢ 0} →
    ℚ.∣ Bishop.seq left n ℚ.- Bishop.seq right n ∣
    ℚ.≤
    (+ 2 / n)
  bounds n with
    ℚP._≤?_
      ℚ.∣ Bishop.seq left n ℚ.- Bishop.seq right n ∣
      (+ 2 / n)
  ... | yes bound = bound
  ... | no notBound =
    ⊥-elim
      (nn
        (λ equality →
          notBound
            (bishopEqualityBound equality n)))

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl value = value

BishopHalfPredicate :
  ∀ {analytic} →
  Located.AnalyticLocatedHeightCarrierAttachment
    analytic
    BishopHeight.bishopLocatedHeightCarrier →
  Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic) →
  Set
BishopHalfPredicate {analytic} attachment s =
  Bishop._≃_
    (cast
      (Located.realCarrierIdentity attachment)
      (Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic) s))
    bishopHalf

record BishopCriticalLineHalfCharacterization
    (analytic : Analytic.AnalyticSubstrate)
    (attachment :
      Located.AnalyticLocatedHeightCarrierAttachment
        analytic
        BishopHeight.bishopLocatedHeightCarrier)
    : Set where
  field
    criticalLineImpliesBishopHalf :
      (s : Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic) s →
      BishopHalfPredicate attachment s

    bishopHalfImpliesCriticalLine :
      (s : Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      BishopHalfPredicate attachment s →
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic) s

open BishopCriticalLineHalfCharacterization public

compileBishopCriticalLinePredicateRefinement :
  ∀ {analytic}
    {attachment :
      Located.AnalyticLocatedHeightCarrierAttachment
        analytic
        BishopHeight.bishopLocatedHeightCarrier} →
  BishopCriticalLineHalfCharacterization analytic attachment →
  Stability.CriticalLinePredicateRefinement analytic
compileBishopCriticalLinePredicateRefinement
    {analytic = analytic} {attachment = attachment} characterization = record
  { Stability.CriticalLinePredicateRefinement.RefinedCritical =
      BishopHalfPredicate attachment
  ; Stability.CriticalLinePredicateRefinement.abstractImpliesRefined =
      criticalLineImpliesBishopHalf characterization
  ; Stability.CriticalLinePredicateRefinement.refinedImpliesAbstract =
      bishopHalfImpliesCriticalLine characterization
  ; Stability.CriticalLinePredicateRefinement.refinedCriticalStable =
      λ s →
        bishopSetoidEqualityStable
          (cast
            (Located.realCarrierIdentity attachment)
            (Analytic.ComplexAnalyticCarrier.realPart
              (Analytic.AnalyticSubstrate.carrier analytic) s))
          bishopHalf
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceipt =
      BishopCriticalLineHalfCharacterization analytic attachment
  ; Stability.CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceiptWitness =
      characterization
  ; Stability.CriticalLinePredicateRefinement.refinementReference =
      "criticalLine iff Bishop-setoid realPart ~= 1/2; equality stability proved from decidable rational bounds"
  }

record BishopSetoidCriticalLineBoundary : Set where
  constructor bishop-setoid-critical-line-boundary
  field
    agdaRecordEqualityUsedAsRealEquality : Bool
    bishopSetoidEqualityUsed : Bool
    bishopSetoidEqualityStableConstructively : Bool
    globalExcludedMiddleUsed : Bool
    criticalLineHalfCharacterizationStillRequired : Bool
    rhDerivedHere : Bool

open BishopSetoidCriticalLineBoundary public

canonicalBishopSetoidCriticalLineBoundary :
  BishopSetoidCriticalLineBoundary
canonicalBishopSetoidCriticalLineBoundary =
  bishop-setoid-critical-line-boundary
    false true true false true false
