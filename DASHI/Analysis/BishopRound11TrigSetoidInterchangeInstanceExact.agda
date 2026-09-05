module DASHI.Analysis.BishopRound11TrigSetoidInterchangeInstanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Real as Bishop
import Sequence as BishopSequence

import DASHI.Analysis.BishopConstructedRealBackendExact as Backend
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.SetoidDerivativeLimitInterchangeBidiExact as Interchange
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Analysis.BishopConcreteTrigonometricDerivativeBidiExact as Concrete
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

------------------------------------------------------------------------
-- ROUND11 BISHOP TRIG -> GENERIC SETOID DERIVATIVE/LIMIT PROBLEM
--
-- The literal function approximants are finite partial sums of the existing
-- Round11 sine/cosine terms.  Their derivative candidates are finite partial
-- sums of the already-owned concrete differentiated terms.  Convergence of the
-- function series and derivative series is imported from the existing Bishop
-- owners.  What remains explicit is:
--   * finite-sum differentiation for the selected derivative semantics;
--   * the actual derivative/limit interchange control.
------------------------------------------------------------------------

BishopSetoidReal : Spine.SetoidOrderedCompleteReal
BishopSetoidReal = Backend.bishopImportedSetoidOrderedCompleteReal

BishopSequences : Spine.FunctionSequenceRealization BishopSetoidReal
BishopSequences =
  Backend.bishopFunctionSequenceRealization
    Backend.bishopImportedAlgebraOrderPackaging

record BishopTrigDerivativeSemantics : Set₁ where
  field
    DerivativeAt :
      (Bishop.ℝ → Bishop.ℝ) →
      Bishop.ℝ → Bishop.ℝ → Set

    finiteSinePartialSumDerivative :
      (dataSet : Elementary.BishopElementaryPowerSeriesData) →
      (count : Nat) →
      (point : Bishop.ℝ) →
      DerivativeAt
        (λ x → BishopSequence.SeriesOf (Elementary.sineTerm dataSet x) count)
        point
        (BishopSequence.SeriesOf
          (Finite.sineAlgebraicDerivedTerm point) count)

    finiteCosinePartialSumDerivative :
      (dataSet : Elementary.BishopElementaryPowerSeriesData) →
      (count : Nat) →
      (point : Bishop.ℝ) →
      DerivativeAt
        (λ x → BishopSequence.SeriesOf (Elementary.cosineTerm dataSet x) count)
        point
        (BishopSequence.SeriesOf
          (Finite.cosineAlgebraicDerivedTerm point) count)

    reading : String

open BishopTrigDerivativeSemantics public

record Round11TrigInterchangeInstance : Set₁ where
  field
    round11 : Round11.Round11BishopCutset
    derivativeSemantics : BishopTrigDerivativeSemantics

    SineInterchangeControlAt : Bishop.ℝ → Set
    CosineInterchangeControlAt : Bishop.ℝ → Set

    sineInterchangeControlMeaning : String
    cosineInterchangeControlMeaning : String
    reading : String

open Round11TrigInterchangeInstance public

seriesData :
  Round11TrigInterchangeInstance →
  Elementary.BishopElementaryPowerSeriesData
seriesData I = Round11.elementarySeries (round11 I)

concreteProblem :
  Round11TrigInterchangeInstance →
  Concrete.ConcreteBishopTrigDerivativeProblem
concreteProblem I = record
  { Concrete.round11 = round11 I
  ; Concrete.derivativeSeriesInterchange =
      (∀ point → SineInterchangeControlAt I point)
      × (∀ point → CosineInterchangeControlAt I point)
  ; Concrete.reading =
      "Round11 literal Bishop sine/cosine object; interchange is split into explicit sine and cosine pointwise control."
  }

sineSetoidProblem :
  (I : Round11TrigInterchangeInstance) →
  Interchange.SetoidDerivativeLimitProblem
sineSetoidProblem I = record
  { Interchange.R = BishopSetoidReal
  ; Interchange.sequences = BishopSequences
  ; Interchange.Domain = Bishop.ℝ
  ; Interchange.approximant = λ count point →
      BishopSequence.SeriesOf (Elementary.sineTerm (seriesData I) point) count
  ; Interchange.derivativeApproximant = λ count point →
      BishopSequence.SeriesOf (Finite.sineAlgebraicDerivedTerm point) count
  ; Interchange.limitFunction = Elementary.bishopSin (seriesData I)
  ; Interchange.derivativeLimit = Elementary.bishopCos (seriesData I)
  ; Interchange.DerivativeAt = DerivativeAt (derivativeSemantics I)
  ; Interchange.approximantDerivative =
      finiteSinePartialSumDerivative (derivativeSemantics I) (seriesData I)
  ; Interchange.FunctionConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Elementary.sineTerm (seriesData I) point))
        (Elementary.bishopSin (seriesData I) point)
  ; Interchange.DerivativeConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Finite.sineAlgebraicDerivedTerm point))
        (Elementary.bishopCos (seriesData I) point)
  ; Interchange.InterchangeControlAt = SineInterchangeControlAt I
  ; Interchange.functionConvergence = Elementary.bishopSinConvergence (seriesData I)
  ; Interchange.derivativeConvergence =
      Concrete.sineDerivedSeriesConverges (concreteProblem I)
  ; Interchange.reading = sineInterchangeControlMeaning I
  }

cosineSetoidProblem :
  (I : Round11TrigInterchangeInstance) →
  Interchange.SetoidDerivativeLimitProblem
cosineSetoidProblem I = record
  { Interchange.R = BishopSetoidReal
  ; Interchange.sequences = BishopSequences
  ; Interchange.Domain = Bishop.ℝ
  ; Interchange.approximant = λ count point →
      BishopSequence.SeriesOf (Elementary.cosineTerm (seriesData I) point) count
  ; Interchange.derivativeApproximant = λ count point →
      BishopSequence.SeriesOf (Finite.cosineAlgebraicDerivedTerm point) count
  ; Interchange.limitFunction = Elementary.bishopCos (seriesData I)
  ; Interchange.derivativeLimit = λ point → Bishop.-_ (Elementary.bishopSin (seriesData I) point)
  ; Interchange.DerivativeAt = DerivativeAt (derivativeSemantics I)
  ; Interchange.approximantDerivative =
      finiteCosinePartialSumDerivative (derivativeSemantics I) (seriesData I)
  ; Interchange.FunctionConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Elementary.cosineTerm (seriesData I) point))
        (Elementary.bishopCos (seriesData I) point)
  ; Interchange.DerivativeConvergesAt = λ point →
      BishopSequence._ConvergesTo_
        (BishopSequence.SeriesOf (Finite.cosineAlgebraicDerivedTerm point))
        (Bishop.-_ (Elementary.bishopSin (seriesData I) point))
  ; Interchange.InterchangeControlAt = CosineInterchangeControlAt I
  ; Interchange.functionConvergence = Elementary.bishopCosConvergence (seriesData I)
  ; Interchange.derivativeConvergence =
      Concrete.cosineDerivedSeriesConverges (concreteProblem I)
  ; Interchange.reading = cosineInterchangeControlMeaning I
  }

record Round11TrigInterchangeAuthorities
    (I : Round11TrigInterchangeInstance) : Set₁ where
  field
    sine : Interchange.SetoidDerivativeLimitInterchangeAuthority (sineSetoidProblem I)
    cosine : Interchange.SetoidDerivativeLimitInterchangeAuthority (cosineSetoidProblem I)

open Round11TrigInterchangeAuthorities public

sineDerivativeCompiled :
  ∀ {I} →
  Round11TrigInterchangeAuthorities I →
  (point : Bishop.ℝ) →
  DerivativeAt (derivativeSemantics I)
    (Elementary.bishopSin (seriesData I))
    point
    (Elementary.bishopCos (seriesData I) point)
sineDerivativeCompiled A =
  Interchange.derivativeOfLimit (sine A)

cosineDerivativeCompiled :
  ∀ {I} →
  Round11TrigInterchangeAuthorities I →
  (point : Bishop.ℝ) →
  DerivativeAt (derivativeSemantics I)
    (Elementary.bishopCos (seriesData I))
    point
    (Bishop.-_ (Elementary.bishopSin (seriesData I) point))
cosineDerivativeCompiled A =
  Interchange.derivativeOfLimit (cosine A)

record ReverseRound11InterchangeObligations : Set where
  field
    derivativeSemanticsSelected : Set
    finitePartialSumRuleClosed : Set
    sineInterchangeControlClosed : Set
    cosineInterchangeControlClosed : Set

open ReverseRound11InterchangeObligations public

record Status : Set where
  field
    literalRound11FunctionConvergenceOwned : Bool
    literalRound11DerivedSeriesConvergenceOwned : Bool
    genericSetoidProblemInstantiationOwned : Bool
    finitePartialSumDerivativeRuleClosed : Bool
    interchangeControlClosed : Bool

    literalRound11FunctionConvergenceOwnedIsTrue : literalRound11FunctionConvergenceOwned ≡ true
    literalRound11DerivedSeriesConvergenceOwnedIsTrue : literalRound11DerivedSeriesConvergenceOwned ≡ true
    genericSetoidProblemInstantiationOwnedIsTrue : genericSetoidProblemInstantiationOwned ≡ true
    finitePartialSumDerivativeRuleClosedIsFalse : finitePartialSumDerivativeRuleClosed ≡ false
    interchangeControlClosedIsFalse : interchangeControlClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { literalRound11FunctionConvergenceOwned = true
  ; literalRound11DerivedSeriesConvergenceOwned = true
  ; genericSetoidProblemInstantiationOwned = true
  ; finitePartialSumDerivativeRuleClosed = false
  ; interchangeControlClosed = false
  ; literalRound11FunctionConvergenceOwnedIsTrue = refl
  ; literalRound11DerivedSeriesConvergenceOwnedIsTrue = refl
  ; genericSetoidProblemInstantiationOwnedIsTrue = refl
  ; finitePartialSumDerivativeRuleClosedIsFalse = refl
  ; interchangeControlClosedIsFalse = refl
  }
