module DASHI.Physics.Closure.NSWholeSpaceBishopCauchyPSDLimitExact where

------------------------------------------------------------------------
-- A / FINITE CAUCHY PSD -> CONTINUOUS-LIMIT PSD
--
-- The Bishop order is closed under convergent limits.  Therefore no new
-- positivity argument is needed at the continuum stage:
--
--   Q_n >= 0 for every finite approximation,
--   Q_n -> Q,
--   -------------------------------
--   Q >= 0.
--
-- NSWholeSpaceBishopComplex3CauchyPSDExact already proves Q_n >= 0 for every
-- finite C^3 Cauchy-resolvent form.  The ONLY analytic input left here is the
-- same-object convergence identifying those finite approximants with the
-- desired continuous Cauchy Gram.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Physics.Closure.NSWholeSpaceBishopComplex3CauchyPSDExact as ComplexPSD

zeroSequence : Nat → BishopReal.ℝ
zeroSequence _ = BishopReal.0ℝ

zeroSequenceConvergent :
  BishopSequence._isConvergent zeroSequence
zeroSequenceConvergent =
  BishopReal.0ℝ
  , BishopSequence.xₙ≃c⇒xₙ→c
      (λ {(suc index) → BishopP.≃-refl})

nonnegativeSequenceLimit :
  (sequence : Nat → BishopReal.ℝ) →
  ((index : Nat) → BishopReal.NonNegative (sequence index)) →
  (limit : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopReal.NonNegative limit
nonnegativeSequenceLimit sequence sequenceNN limit convergence =
  let
    zeroBelow :
      (index : Nat) →
      BishopReal._≤_ (zeroSequence index) (sequence index)
    zeroBelow index =
      BishopP.nonNegx⇒0≤x (sequenceNN index)

    limitOrder :
      BishopReal._≤_ BishopReal.0ℝ limit
    limitOrder =
      BishopSequence.xₙ≤yₙ⇒limxₙ≤limyₙ
        zeroBelow
        zeroSequenceConvergent
        (limit , convergence)
  in
  BishopP.0≤x⇒nonNegx limitOrder

record FiniteCauchyApproximationToContinuous
    (continuousCauchyGram : BishopReal.ℝ) : Set₁ where
  constructor finite-cauchy-approximation-to-continuous
  field
    cells :
      Nat → List ComplexPSD.PositiveRateComplex3Cell

    finiteForm :
      Nat → BishopReal.ℝ
    finiteFormMeaning :
      (index : Nat) →
      BishopReal._≃_
        (finiteForm index)
        (ComplexPSD.hermitianCauchyForm (cells index))

    finiteFormsConverge :
      BishopSequence._ConvergesTo_
        finiteForm
        continuousCauchyGram

open FiniteCauchyApproximationToContinuous public

finiteApproximationFormNonnegative :
  ∀ {continuousCauchyGram} →
  (A : FiniteCauchyApproximationToContinuous continuousCauchyGram) →
  (index : Nat) →
  BishopReal.NonNegative (finiteForm A index)
finiteApproximationFormNonnegative A index =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm (finiteFormMeaning A index))
      (BishopP.nonNegx⇒0≤x
        (ComplexPSD.hermitianCauchyFormNonnegative
          (cells A index))))

continuousCauchyGramNonnegative :
  ∀ {continuousCauchyGram} →
  FiniteCauchyApproximationToContinuous continuousCauchyGram →
  BishopReal.NonNegative continuousCauchyGram
continuousCauchyGramNonnegative {continuousCauchyGram} A =
  nonnegativeSequenceLimit
    (finiteForm A)
    (finiteApproximationFormNonnegative A)
    continuousCauchyGram
    (finiteFormsConverge A)

limitOrderClosurePaid : Bool
limitOrderClosurePaid = true

finiteCauchyKernelPSDReused : Bool
finiteCauchyKernelPSDReused = true

continuousPSDNeedsNewKernelInequality : Bool
continuousPSDNeedsNewKernelInequality = false

continuousPSDNeedsSameObjectApproximationConvergence : Bool
continuousPSDNeedsSameObjectApproximationConvergence = true

clayPromotion : Bool
clayPromotion = false

limitOrderClosurePaidIsTrue :
  limitOrderClosurePaid ≡ true
limitOrderClosurePaidIsTrue = refl

finiteCauchyKernelPSDReusedIsTrue :
  finiteCauchyKernelPSDReused ≡ true
finiteCauchyKernelPSDReusedIsTrue = refl

continuousPSDNeedsNewKernelInequalityIsFalse :
  continuousPSDNeedsNewKernelInequality ≡ false
continuousPSDNeedsNewKernelInequalityIsFalse = refl

continuousPSDNeedsSameObjectApproximationConvergenceIsTrue :
  continuousPSDNeedsSameObjectApproximationConvergence ≡ true
continuousPSDNeedsSameObjectApproximationConvergenceIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
