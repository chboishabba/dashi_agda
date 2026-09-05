module DASHI.Analysis.BishopTrigFinitePartialSumAnalyticDerivativeExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopConstructedRealBackendExact as Backend
import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopConcreteTrigAnalyticTermDerivativeExact as TermAnalytic
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Analysis.SetoidFiniteSumDerivativeBidiExact as FiniteSum
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms

------------------------------------------------------------------------
-- BISHOP TRIG FINITE PARTIAL SUM ANALYTIC DERIVATIVES
------------------------------------------------------------------------

bishopFactorAdditiveSemantics : FiniteSum.SetoidDerivativeAdditiveSemantics
bishopFactorAdditiveSemantics = record
  { FiniteSum.R = Backend.bishopImportedSetoidOrderedCompleteReal
  ; FiniteSum.Domain = Bishop.ℝ
  ; FiniteSum.DerivativeAt = Factor.BishopFactorDerivativeAt
  ; FiniteSum.zeroDerivative = Factor.factorDerivativeZero
  ; FiniteSum.addDerivative = Factor.factorDerivativeAdd
  ; FiniteSum.reading =
      "Bishop division-free factor derivative instantiated as the generic additive finite-sum derivative semantics."
  }

sineTermFamily : Nat → Bishop.ℝ → Bishop.ℝ
sineTermFamily index point = Terms.sineSignedTerm point index

sineDerivativeTermFamily : Nat → Bishop.ℝ → Bishop.ℝ
sineDerivativeTermFamily index point =
  Finite.sineAlgebraicDerivedTerm point index

sineFinitePartialDerivative :
  ∀ count point →
  Factor.BishopFactorDerivativeAt
    (FiniteSum.finitePartialSum
      bishopFactorAdditiveSemantics sineTermFamily count)
    point
    (FiniteSum.finitePartialDerivativeSum
      bishopFactorAdditiveSemantics sineDerivativeTermFamily count point)
sineFinitePartialDerivative =
  FiniteSum.finiteSumDerivative
    bishopFactorAdditiveSemantics
    (λ index point → TermAnalytic.sineTermAnalyticDerivative point index)

------------------------------------------------------------------------
-- Cosine: isolate the constant n=0 term, then differentiate the shifted tail.
------------------------------------------------------------------------

cosineShiftedTermFamily : Nat → Bishop.ℝ → Bishop.ℝ
cosineShiftedTermFamily index point =
  Terms.cosineSignedTerm point (suc index)

cosineShiftedDerivativeTermFamily : Nat → Bishop.ℝ → Bishop.ℝ
cosineShiftedDerivativeTermFamily index point =
  Finite.cosineAlgebraicDerivedTerm point index

cosineShiftedFiniteDerivative :
  ∀ count point →
  Factor.BishopFactorDerivativeAt
    (FiniteSum.finitePartialSum
      bishopFactorAdditiveSemantics cosineShiftedTermFamily count)
    point
    (FiniteSum.finitePartialDerivativeSum
      bishopFactorAdditiveSemantics
      cosineShiftedDerivativeTermFamily count point)
cosineShiftedFiniteDerivative =
  FiniteSum.finiteSumDerivative
    bishopFactorAdditiveSemantics
    (λ index point →
      TermAnalytic.cosineSuccessorTermAnalyticDerivative point index)

factorDerivativeConstant :
  ∀ constant point →
  Factor.BishopFactorDerivativeAt
    (λ _ → constant)
    point Bishop.0ℝ
factorDerivativeConstant constant point = record
  { Factor.quotient = λ _ → Bishop.0ℝ
  ; Factor.incrementFactorisation = λ h →
      let open BishopP.ℝ-Solver
      in solve 2
        (λ c h′ → c ⊖ c ⊜ h′ ⊗ Κ 0ℚᵘ)
        BishopP.≃-refl constant h
  ; Factor.quotientConvergesOnNullSequences = λ perturbationConverges →
      import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as PowerFactor
      in PowerFactor.constantConverges Bishop.0ℝ
  }

cosineZeroTermIsOne :
  ∀ point →
  Bishop._≃_
    (Terms.cosineSignedTerm point zero)
    Bishop.1ℝ
cosineZeroTermIsOne point =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊜ Κ 1ℚᵘ)
    BishopP.≃-refl

cosineZeroTermDerivative :
  ∀ point →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.cosineSignedTerm value zero)
    point Bishop.0ℝ
cosineZeroTermDerivative point =
  Factor.factorDerivativeCongruence
    cosineZeroTermIsOne
    BishopP.≃-refl
    (factorDerivativeConstant Bishop.1ℝ point)

cosineOffsetPartial : Nat → Bishop.ℝ → Bishop.ℝ
cosineOffsetPartial count point =
  Bishop._+_
    (Terms.cosineSignedTerm point zero)
    (FiniteSum.finitePartialSum
      bishopFactorAdditiveSemantics
      cosineShiftedTermFamily count point)

cosineOffsetDerivativePartial : Nat → Bishop.ℝ → Bishop.ℝ
cosineOffsetDerivativePartial count point =
  FiniteSum.finitePartialDerivativeSum
    bishopFactorAdditiveSemantics
    cosineShiftedDerivativeTermFamily count point

cosineOffsetPartialDerivative :
  ∀ count point →
  Factor.BishopFactorDerivativeAt
    (cosineOffsetPartial count)
    point
    (cosineOffsetDerivativePartial count point)
cosineOffsetPartialDerivative count point =
  Factor.factorDerivativeCongruence
    (λ _ → BishopP.≃-refl)
    (BishopP.+-identityˡ (cosineOffsetDerivativePartial count point))
    (Factor.factorDerivativeAdd
      (cosineZeroTermDerivative point)
      (cosineShiftedFiniteDerivative count point))

------------------------------------------------------------------------
-- Literal Bishop SeriesOf welds.
------------------------------------------------------------------------

sineGenericPartialIsSeriesOf :
  ∀ count point →
  Bishop._≃_
    (FiniteSum.finitePartialSum
      bishopFactorAdditiveSemantics sineTermFamily count point)
    (BishopSequence.SeriesOf (Terms.sineSignedTerm point) count)
sineGenericPartialIsSeriesOf zero point = BishopP.≃-refl
sineGenericPartialIsSeriesOf (suc count) point =
  BishopP.+-cong
    (sineGenericPartialIsSeriesOf count point)
    BishopP.≃-refl

sineGenericDerivativePartialIsSeriesOf :
  ∀ count point →
  Bishop._≃_
    (FiniteSum.finitePartialDerivativeSum
      bishopFactorAdditiveSemantics sineDerivativeTermFamily count point)
    (BishopSequence.SeriesOf
      (Finite.sineAlgebraicDerivedTerm point) count)
sineGenericDerivativePartialIsSeriesOf zero point = BishopP.≃-refl
sineGenericDerivativePartialIsSeriesOf (suc count) point =
  BishopP.+-cong
    (sineGenericDerivativePartialIsSeriesOf count point)
    BishopP.≃-refl

sineSeriesPartialAnalyticDerivative :
  ∀ count point →
  Factor.BishopFactorDerivativeAt
    (λ value → BishopSequence.SeriesOf (Terms.sineSignedTerm value) count)
    point
    (BishopSequence.SeriesOf
      (Finite.sineAlgebraicDerivedTerm point) count)
sineSeriesPartialAnalyticDerivative count point =
  Factor.factorDerivativeCongruence
    (λ value → sineGenericPartialIsSeriesOf count value)
    (sineGenericDerivativePartialIsSeriesOf count point)
    (sineFinitePartialDerivative count point)

cosineOffsetIsSeriesOf :
  ∀ count point →
  Bishop._≃_
    (cosineOffsetPartial count point)
    (BishopSequence.SeriesOf (Terms.cosineSignedTerm point) (suc count))
cosineOffsetIsSeriesOf zero point =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ c → c ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ c)
    BishopP.≃-refl
    (Terms.cosineSignedTerm point zero)
cosineOffsetIsSeriesOf (suc count) point =
  let
    c0 = Terms.cosineSignedTerm point zero
    tail = FiniteSum.finitePartialSum
      bishopFactorAdditiveSemantics cosineShiftedTermFamily count point
    next = Terms.cosineSignedTerm point (suc count)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ first old next′ →
        first ⊕ (old ⊕ next′) ⊜ (first ⊕ old) ⊕ next′)
      BishopP.≃-refl c0 tail next)
    (BishopP.+-cong
      (cosineOffsetIsSeriesOf count point)
      BishopP.≃-refl)

cosineOffsetDerivativeIsSeriesOf :
  ∀ count point →
  Bishop._≃_
    (cosineOffsetDerivativePartial count point)
    (BishopSequence.SeriesOf
      (Finite.cosineAlgebraicDerivedTerm point) count)
cosineOffsetDerivativeIsSeriesOf zero point = BishopP.≃-refl
cosineOffsetDerivativeIsSeriesOf (suc count) point =
  BishopP.+-cong
    (cosineOffsetDerivativeIsSeriesOf count point)
    BishopP.≃-refl

cosineSeriesOffsetPartialAnalyticDerivative :
  ∀ count point →
  Factor.BishopFactorDerivativeAt
    (λ value →
      BishopSequence.SeriesOf
        (Terms.cosineSignedTerm value)
        (suc count))
    point
    (BishopSequence.SeriesOf
      (Finite.cosineAlgebraicDerivedTerm point) count)
cosineSeriesOffsetPartialAnalyticDerivative count point =
  Factor.factorDerivativeCongruence
    (λ value → cosineOffsetIsSeriesOf count value)
    (cosineOffsetDerivativeIsSeriesOf count point)
    (cosineOffsetPartialDerivative count point)

record Status : Set where
  field
    additiveFactorDerivativeInstantiated : Bool
    sineLiteralFinitePartialDerivativeOwned : Bool
    cosineZeroModeDerivativeOwned : Bool
    cosineLiteralOffsetFinitePartialDerivativeOwned : Bool

    additiveFactorDerivativeInstantiatedIsTrue : additiveFactorDerivativeInstantiated ≡ true
    sineLiteralFinitePartialDerivativeOwnedIsTrue : sineLiteralFinitePartialDerivativeOwned ≡ true
    cosineZeroModeDerivativeOwnedIsTrue : cosineZeroModeDerivativeOwned ≡ true
    cosineLiteralOffsetFinitePartialDerivativeOwnedIsTrue :
      cosineLiteralOffsetFinitePartialDerivativeOwned ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { additiveFactorDerivativeInstantiated = true
  ; sineLiteralFinitePartialDerivativeOwned = true
  ; cosineZeroModeDerivativeOwned = true
  ; cosineLiteralOffsetFinitePartialDerivativeOwned = true
  ; additiveFactorDerivativeInstantiatedIsTrue = refl
  ; sineLiteralFinitePartialDerivativeOwnedIsTrue = refl
  ; cosineZeroModeDerivativeOwnedIsTrue = refl
  ; cosineLiteralOffsetFinitePartialDerivativeOwnedIsTrue = refl
  }
