module DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import Real as Bishop
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopConstructedRealBackendExact as Backend
import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopTrigFinitePartialSumAnalyticDerivativeExact as Partial
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Analysis.BishopConcreteTrigonometricDerivativeBidiExact as Derived
import DASHI.Analysis.SetoidDerivativeLimitInterchangeBidiExact as Interchange
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopConcreteSeriesConvergenceTransportExact as Transport
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

------------------------------------------------------------------------
-- ROUND11 FACTOR-DERIVATIVE INTERCHANGE INSTANCE
--
-- All finite and pointwise-convergence obligations are now machine-produced:
--   * literal signed-term analytic derivatives,
--   * literal finite partial-sum analytic derivatives,
--   * concrete signed-series convergence to the Round11 sine/cosine values,
--   * derivative-series convergence to cosine / minus-sine.
--
-- The only remaining theorem family is the genuine infinite-limit derivative
-- interchange control.
------------------------------------------------------------------------

record Round11FactorInterchangeProblem : Set₁ where
  field
    round11 : Round11.Round11BishopCutset

    SineInterchangeControlAt : Bishop.ℝ → Set
    CosineInterchangeControlAt : Bishop.ℝ → Set

    sineControlReading : String
    cosineControlReading : String
    reading : String

open Round11FactorInterchangeProblem public

dataSet : Round11FactorInterchangeProblem → Elementary.BishopElementaryPowerSeriesData
dataSet P = Round11.elementarySeries (round11 P)

termIdentification :
  (P : Round11FactorInterchangeProblem) →
  Terms.ConcreteSineCosineTermIdentification (dataSet P)
termIdentification P =
  Round11.round11ConcreteTermIdentification (round11 P)

concreteDerivativeProblem :
  Round11FactorInterchangeProblem →
  Derived.ConcreteBishopTrigDerivativeProblem
concreteDerivativeProblem P = record
  { Derived.round11 = round11 P
  ; Derived.derivativeSeriesInterchange =
      (∀ point → SineInterchangeControlAt P point)
      × (∀ point → CosineInterchangeControlAt P point)
  ; Derived.reading =
      "Concrete Round11 derivative-series convergence; only the final interchange theorem remains."
  }

concreteSineSeriesConverges :
  (P : Round11FactorInterchangeProblem) →
  (point : Bishop.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
    (Elementary.bishopSin (dataSet P) point)
concreteSineSeriesConverges P point =
  Transport.pointwiseEquivalentSeriesConvergence
    (Terms.sineTermIsConcrete (termIdentification P) point)
    (Elementary.bishopSinConvergence (dataSet P) point)

concreteCosineSeriesConverges :
  (P : Round11FactorInterchangeProblem) →
  (point : Bishop.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (Terms.cosineSignedTerm point))
    (Elementary.bishopCos (dataSet P) point)
concreteCosineSeriesConverges P point =
  Transport.pointwiseEquivalentSeriesConvergence
    (Terms.cosineTermIsConcrete (termIdentification P) point)
    (Elementary.bishopCosConvergence (dataSet P) point)

cosineOffsetSeriesConverges :
  (P : Round11FactorInterchangeProblem) →
  (point : Bishop.ℝ) →
  BishopSequence._ConvergesTo_
    (λ count →
      BishopSequence.SeriesOf
        (Terms.cosineSignedTerm point)
        (suc count))
    (Elementary.bishopCos (dataSet P) point)
cosineOffsetSeriesConverges P point =
  BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (BishopSequence.shift-is-subsequence
      (BishopSequence.SeriesOf (Terms.cosineSignedTerm point)) 1)
    (Elementary.bishopCos (dataSet P) point ,
      concreteCosineSeriesConverges P point)

sineProblem :
  (P : Round11FactorInterchangeProblem) →
  Interchange.SetoidDerivativeLimitProblem
sineProblem P = record
  { Interchange.R = Backend.bishopImportedSetoidOrderedCompleteReal
  ; Interchange.sequences =
      Backend.bishopFunctionSequenceRealization
        Backend.bishopImportedAlgebraOrderPackaging
  ; Interchange.Domain = Bishop.ℝ
  ; Interchange.approximant = λ count point →
      BishopSequence.SeriesOf (Terms.sineSignedTerm point) count
  ; Interchange.derivativeApproximant = λ count point →
      BishopSequence.SeriesOf
        (Finite.sineAlgebraicDerivedTerm point) count
  ; Interchange.limitFunction = Elementary.bishopSin (dataSet P)
  ; Interchange.derivativeLimit = Elementary.bishopCos (dataSet P)
  ; Interchange.DerivativeAt = Factor.BishopFactorDerivativeAt
  ; Interchange.approximantDerivative =
      Partial.sineSeriesPartialAnalyticDerivative
  ; Interchange.FunctionConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Terms.sineSignedTerm point))
        (Elementary.bishopSin (dataSet P) point)
  ; Interchange.DerivativeConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf
          (Finite.sineAlgebraicDerivedTerm point))
        (Elementary.bishopCos (dataSet P) point)
  ; Interchange.InterchangeControlAt = SineInterchangeControlAt P
  ; Interchange.functionConvergence = concreteSineSeriesConverges P
  ; Interchange.derivativeConvergence =
      Derived.sineDerivedSeriesConverges (concreteDerivativeProblem P)
  ; Interchange.reading = sineControlReading P
  }

cosineProblem :
  (P : Round11FactorInterchangeProblem) →
  Interchange.SetoidDerivativeLimitProblem
cosineProblem P = record
  { Interchange.R = Backend.bishopImportedSetoidOrderedCompleteReal
  ; Interchange.sequences =
      Backend.bishopFunctionSequenceRealization
        Backend.bishopImportedAlgebraOrderPackaging
  ; Interchange.Domain = Bishop.ℝ
  ; Interchange.approximant = λ count point →
      BishopSequence.SeriesOf
        (Terms.cosineSignedTerm point)
        (suc count)
  ; Interchange.derivativeApproximant = λ count point →
      BishopSequence.SeriesOf
        (Finite.cosineAlgebraicDerivedTerm point) count
  ; Interchange.limitFunction = Elementary.bishopCos (dataSet P)
  ; Interchange.derivativeLimit = λ point →
      Bishop.-_ (Elementary.bishopSin (dataSet P) point)
  ; Interchange.DerivativeAt = Factor.BishopFactorDerivativeAt
  ; Interchange.approximantDerivative =
      Partial.cosineSeriesOffsetPartialAnalyticDerivative
  ; Interchange.FunctionConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (λ count →
          BishopSequence.SeriesOf
            (Terms.cosineSignedTerm point)
            (suc count))
        (Elementary.bishopCos (dataSet P) point)
  ; Interchange.DerivativeConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf
          (Finite.cosineAlgebraicDerivedTerm point))
        (Bishop.-_ (Elementary.bishopSin (dataSet P) point))
  ; Interchange.InterchangeControlAt = CosineInterchangeControlAt P
  ; Interchange.functionConvergence = cosineOffsetSeriesConverges P
  ; Interchange.derivativeConvergence =
      Derived.cosineDerivedSeriesConverges (concreteDerivativeProblem P)
  ; Interchange.reading = cosineControlReading P
  }

record Round11FactorInterchangeAuthority
    (P : Round11FactorInterchangeProblem) : Set₁ where
  field
    sine : Interchange.SetoidDerivativeLimitInterchangeAuthority (sineProblem P)
    cosine : Interchange.SetoidDerivativeLimitInterchangeAuthority (cosineProblem P)

open Round11FactorInterchangeAuthority public

sineDerivative :
  ∀ {P} →
  Round11FactorInterchangeAuthority P →
  (point : Bishop.ℝ) →
  Factor.BishopFactorDerivativeAt
    (Elementary.bishopSin (dataSet P))
    point
    (Elementary.bishopCos (dataSet P) point)
sineDerivative A = Interchange.derivativeOfLimit (sine A)

cosineDerivative :
  ∀ {P} →
  Round11FactorInterchangeAuthority P →
  (point : Bishop.ℝ) →
  Factor.BishopFactorDerivativeAt
    (Elementary.bishopCos (dataSet P))
    point
    (Bishop.-_ (Elementary.bishopSin (dataSet P) point))
cosineDerivative A = Interchange.derivativeOfLimit (cosine A)

record ReverseRound11FactorInterchangeObligations : Set where
  field
    sineInterchangeControlOnly : Set
    cosineInterchangeControlOnly : Set

open ReverseRound11FactorInterchangeObligations public

record Status : Set where
  field
    powerAnalyticDerivativeOwned : Bool
    literalTrigTermAnalyticDerivativeOwned : Bool
    literalFinitePartialDerivativeOwned : Bool
    functionSeriesConvergenceOwned : Bool
    derivativeSeriesConvergenceOwned : Bool
    finitePartialDerivativeLeafEliminated : Bool
    derivativeLimitInterchangeClosed : Bool

    powerAnalyticDerivativeOwnedIsTrue : powerAnalyticDerivativeOwned ≡ true
    literalTrigTermAnalyticDerivativeOwnedIsTrue : literalTrigTermAnalyticDerivativeOwned ≡ true
    literalFinitePartialDerivativeOwnedIsTrue : literalFinitePartialDerivativeOwned ≡ true
    functionSeriesConvergenceOwnedIsTrue : functionSeriesConvergenceOwned ≡ true
    derivativeSeriesConvergenceOwnedIsTrue : derivativeSeriesConvergenceOwned ≡ true
    finitePartialDerivativeLeafEliminatedIsTrue : finitePartialDerivativeLeafEliminated ≡ true
    derivativeLimitInterchangeClosedIsFalse : derivativeLimitInterchangeClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { powerAnalyticDerivativeOwned = true
  ; literalTrigTermAnalyticDerivativeOwned = true
  ; literalFinitePartialDerivativeOwned = true
  ; functionSeriesConvergenceOwned = true
  ; derivativeSeriesConvergenceOwned = true
  ; finitePartialDerivativeLeafEliminated = true
  ; derivativeLimitInterchangeClosed = false
  ; powerAnalyticDerivativeOwnedIsTrue = refl
  ; literalTrigTermAnalyticDerivativeOwnedIsTrue = refl
  ; literalFinitePartialDerivativeOwnedIsTrue = refl
  ; functionSeriesConvergenceOwnedIsTrue = refl
  ; derivativeSeriesConvergenceOwnedIsTrue = refl
  ; finitePartialDerivativeLeafEliminatedIsTrue = refl
  ; derivativeLimitInterchangeClosedIsFalse = refl
  }
