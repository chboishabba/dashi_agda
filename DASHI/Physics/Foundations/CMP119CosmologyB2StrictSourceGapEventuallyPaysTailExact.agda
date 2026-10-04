{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyB2StrictSourceGapEventuallyPaysTailExact where

------------------------------------------------------------------------
-- B2 SOURCE MAX-CUT: STRICT EQ.(2.23) GAP + STANDARD DYADIC TAIL DECAY.
--
-- The previous B2 source receipt charged the quantitative inequality
--
--   M_ERB + Tail_109(k) < - c_V
--
-- at a selected cutoff.  That is stronger than the actual source physics if
-- the Round109 tail is already known to vanish.  The physical sign theorem is
-- only the strict coefficient gap
--
--   M_ERB < - c_V.
--
-- Ordinary geometric-tail analysis then chooses a sufficiently late cutoff at
-- which the tail fits inside that strict gap.  This module isolates precisely
-- that separation.  The `R109TailEventuallyFitsStrictGap` record is generic
-- convergence/order authority, not new Yang--Mills sign information.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (Σ; _,_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109

record R109TailEventuallyFitsStrictGap
    (source : R109.SourceNativeStressScaleCauchy) : Set₁ where
  field
    eventuallyFits :
      ∀ {base ceiling : ℚ} →
      base < ceiling →
      Σ Nat (λ cutoff →
        base + Tail.r109RemainingTail source cutoff < ceiling)

open R109TailEventuallyFitsStrictGap public

strictSourceGapEventuallyPaysQuantitativeB2 :
  ∀ (source : R109.SourceNativeStressScaleCauchy)
    (tailDecay : R109TailEventuallyFitsStrictGap source)
    {erbCoefficient vacuumCeiling : ℚ} →
  erbCoefficient < vacuumCeiling →
  Σ Nat (λ cutoff →
    erbCoefficient + Tail.r109RemainingTail source cutoff
      < vacuumCeiling)
strictSourceGapEventuallyPaysQuantitativeB2
    source tailDecay strictGap =
  eventuallyFits tailDecay strictGap

strictCoefficientGapIsSourcePhysics : Bool
strictCoefficientGapIsSourcePhysics = true

dyadicTailDecayIsGenericAnalysis : Bool
dyadicTailDecayIsGenericAnalysis = true

quantitativeTailMarginNeedNotBePrimitive : Bool
quantitativeTailMarginNeedNotBePrimitive = true

b2CanMoveToLateCutoffOnlyWhenB1IsAvailableAtThatCutoff : Bool
b2CanMoveToLateCutoffOnlyWhenB1IsAvailableAtThatCutoff = true
