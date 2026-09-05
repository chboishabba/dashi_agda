module DASHI.Analysis.BishopConcreteTrigonometricDerivativeBidiExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Real as Bishop
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Analysis.BishopTrigonometricDerivedSeriesConvergenceExact as Derived
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

------------------------------------------------------------------------
-- CONCRETE BISHOP TRIGONOMETRIC DERIVATIVE, BIDI
--
-- Round11 already packages the literal Bishop elementary sine/cosine series
-- together with their identification with the concrete signed factorial terms.
-- The new finite derivative owner differentiates those concrete terms exactly.
-- The derived-series convergence owner then transports the resulting term
-- identities back to the literal existing Bishop cosine and minus-sine limits.
--
-- Hence finite coefficient differentiation and derived-series convergence are
-- compiler output from an existing Round11 Bishop cutset.  Only the genuinely
-- analytic derivative/series interchange remains as an independent calculus
-- obligation.
------------------------------------------------------------------------

record ConcreteBishopTrigDerivativeProblem : Set₁ where
  field
    round11 : Round11.Round11BishopCutset
    derivativeSeriesInterchange : Set
    reading : String

open ConcreteBishopTrigDerivativeProblem public

dataSet : ConcreteBishopTrigDerivativeProblem → Elementary.BishopElementaryPowerSeriesData
dataSet P = Round11.elementarySeries (round11 P)

termIdentification :
  (P : ConcreteBishopTrigDerivativeProblem) →
  Terms.ConcreteSineCosineTermIdentification (dataSet P)
termIdentification P =
  Round11.round11ConcreteTermIdentification (round11 P)

concreteDerivedTermIdentification :
  (P : ConcreteBishopTrigDerivativeProblem) →
  Derived.TrigonometricDerivedTermIdentification (dataSet P)
concreteDerivedTermIdentification P = record
  { Derived.sineDerivedTerm = Finite.sineAlgebraicDerivedTerm
  ; Derived.cosineDerivedTerm = Finite.cosineAlgebraicDerivedTerm
  ; Derived.sineDerivedTermIsCosineTerm = λ point index →
      BishopP.≃-trans
        (Finite.sineFiniteTermDerivativeIsCosineTerm point index)
        (BishopP.≃-symm
          (Terms.cosineTermIsConcrete (termIdentification P) point index))
  ; Derived.cosineDerivedTermIsNegativeSineTerm = λ point index →
      BishopP.≃-trans
        (Finite.cosineFiniteTermDerivativeIsNegativeSineTerm point index)
        (BishopP.-‿cong
          (BishopP.≃-symm
            (Terms.sineTermIsConcrete (termIdentification P) point index)))
  }

sineDerivedSeriesConverges :
  (P : ConcreteBishopTrigDerivativeProblem) →
  (point : Bishop.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Finite.sineAlgebraicDerivedTerm point))
    (Elementary.bishopCos (dataSet P) point)
sineDerivedSeriesConverges P =
  Derived.sineDerivedSeriesConvergesToCosine
    (concreteDerivedTermIdentification P)

cosineDerivedSeriesConverges :
  (P : ConcreteBishopTrigDerivativeProblem) →
  (point : Bishop.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Finite.cosineAlgebraicDerivedTerm point))
    (Bishop.-_ (Elementary.bishopSin (dataSet P) point))
cosineDerivedSeriesConverges P =
  Derived.cosineDerivedSeriesConvergesToNegativeSine
    (concreteDerivedTermIdentification P)

record ConcreteBishopTrigDerivativeReceipt
    (P : ConcreteBishopTrigDerivativeProblem) : Set₁ where
  field
    interchangeClosed : derivativeSeriesInterchange P

    SineDerivativeAt : Bishop.ℝ → Set
    CosineDerivativeAt : Bishop.ℝ → Set

    sineDerivativeFromInterchange :
      derivativeSeriesInterchange P →
      (point : Bishop.ℝ) →
      SineDerivativeAt point

    cosineDerivativeFromInterchange :
      derivativeSeriesInterchange P →
      (point : Bishop.ℝ) →
      CosineDerivativeAt point

open ConcreteBishopTrigDerivativeReceipt public

compileSineDerivative :
  ∀ {P} →
  (R : ConcreteBishopTrigDerivativeReceipt P) →
  (point : Bishop.ℝ) →
  SineDerivativeAt R point
compileSineDerivative R =
  sineDerivativeFromInterchange R (interchangeClosed R)

compileCosineDerivative :
  ∀ {P} →
  (R : ConcreteBishopTrigDerivativeReceipt P) →
  (point : Bishop.ℝ) →
  CosineDerivativeAt R point
compileCosineDerivative R =
  cosineDerivativeFromInterchange R (interchangeClosed R)

record ReverseConcreteTrigObligations : Set where
  field
    round11LiteralSeriesObjectSelected : Set
    derivativeSeriesInterchangeOnly : Set

open ReverseConcreteTrigObligations public

data FiniteTermDerivativeAutomaticallyIsInfiniteSeriesDerivative : Set where

finiteStillDoesNotAutoInterchange :
  FiniteTermDerivativeAutomaticallyIsInfiniteSeriesDerivative → ⊥
finiteStillDoesNotAutoInterchange ()

record Status : Set where
  field
    round11ConcreteTermIdentificationOwned : Bool
    bishopPowerDerivativeOwned : Bool
    inverseFactorialDerivativeCoefficientOwned : Bool
    finiteSineTermDerivativeOwned : Bool
    finiteCosineTermDerivativeOwned : Bool
    sineDerivedSeriesConvergenceOwned : Bool
    cosineDerivedSeriesConvergenceOwned : Bool
    derivativeSeriesInterchangeClosed : Bool

    round11ConcreteTermIdentificationOwnedIsTrue :
      round11ConcreteTermIdentificationOwned ≡ true
    bishopPowerDerivativeOwnedIsTrue : bishopPowerDerivativeOwned ≡ true
    inverseFactorialDerivativeCoefficientOwnedIsTrue :
      inverseFactorialDerivativeCoefficientOwned ≡ true
    finiteSineTermDerivativeOwnedIsTrue : finiteSineTermDerivativeOwned ≡ true
    finiteCosineTermDerivativeOwnedIsTrue : finiteCosineTermDerivativeOwned ≡ true
    sineDerivedSeriesConvergenceOwnedIsTrue : sineDerivedSeriesConvergenceOwned ≡ true
    cosineDerivedSeriesConvergenceOwnedIsTrue : cosineDerivedSeriesConvergenceOwned ≡ true
    derivativeSeriesInterchangeClosedIsFalse : derivativeSeriesInterchangeClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { round11ConcreteTermIdentificationOwned = true
  ; bishopPowerDerivativeOwned = true
  ; inverseFactorialDerivativeCoefficientOwned = true
  ; finiteSineTermDerivativeOwned = true
  ; finiteCosineTermDerivativeOwned = true
  ; sineDerivedSeriesConvergenceOwned = true
  ; cosineDerivedSeriesConvergenceOwned = true
  ; derivativeSeriesInterchangeClosed = false
  ; round11ConcreteTermIdentificationOwnedIsTrue = refl
  ; bishopPowerDerivativeOwnedIsTrue = refl
  ; inverseFactorialDerivativeCoefficientOwnedIsTrue = refl
  ; finiteSineTermDerivativeOwnedIsTrue = refl
  ; finiteCosineTermDerivativeOwnedIsTrue = refl
  ; sineDerivedSeriesConvergenceOwnedIsTrue = refl
  ; cosineDerivedSeriesConvergenceOwnedIsTrue = refl
  ; derivativeSeriesInterchangeClosedIsFalse = refl
  }
