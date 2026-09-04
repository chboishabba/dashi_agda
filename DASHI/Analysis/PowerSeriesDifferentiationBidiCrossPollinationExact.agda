module DASHI.Analysis.PowerSeriesDifferentiationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- POWER-SERIES DIFFERENTIATION, BIDI CROSS-POLLINATION
--
-- Shared theorem shape needed by both:
--   * Yang--Mills Bishop sine/cosine coefficient/tail work;
--   * Casimir polar-coordinate trig derivative entries.
--
-- The finite coefficient identity, convergence of the derived series, and
-- interchange of derivative with the series limit are deliberately separate.
------------------------------------------------------------------------

data Lane : Set where
  yangMills casimir : Lane

record PowerSeriesDerivativeProblem : Set₁ where
  field
    Point Value : Set
    term derivativeTerm : Nat → Point → Value
    partialSum derivativePartialSum : Nat → Point → Value
    sum derivativeCandidate : Point → Value

    DerivativeAt : (Point → Value) → Point → Value → Set
    ConvergesAt : (Nat → Value) → Value → Set

    finiteCoefficientDerivative : Set
    partialSumDerivative : Set
    derivedSeriesConverges : Set
    originalSeriesConverges : Set
    derivativeLimitInterchange : Set
    reading : String

open PowerSeriesDerivativeProblem public

record PowerSeriesDerivativeReceipt
    (P : PowerSeriesDerivativeProblem) : Set₁ where
  field
    finiteCoefficientClosed : finiteCoefficientDerivative P
    partialDerivativeClosed : partialSumDerivative P
    derivedConvergenceClosed : derivedSeriesConverges P
    originalConvergenceClosed : originalSeriesConverges P
    interchangeClosed : derivativeLimitInterchange P

    derivativeOfSum : ∀ x →
      DerivativeAt P (sum P) x (derivativeCandidate P x)

open PowerSeriesDerivativeReceipt public

record ReverseDerivativeObligations : Set where
  field
    coefficientRecurrence : Set
    finitePartialSumDerivative : Set
    derivedTailEstimate : Set
    originalTailEstimate : Set
    limitInterchange : Set
    sameFunctionAsConsumer : Set
    sameDerivativeSemantics : Set

open ReverseDerivativeObligations public

record CrossPollinationEdge : Set where
  field
    source target : Lane
    theoremShapeReusable : Bool
    applicationReceiptReusable : Bool
    reading : String

open CrossPollinationEdge public

yangMillsToCasimirTrigDerivative : CrossPollinationEdge
yangMillsToCasimirTrigDerivative = record
  { source = yangMills
  ; target = casimir
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "YM sine/cosine coefficient and tail work supplies the theorem shape for Casimir polar trig derivatives; no YM application receipt is imported."
  }

casimirToYangMillsDerivativeSeam : CrossPollinationEdge
casimirToYangMillsDerivativeSeam = record
  { source = casimir
  ; target = yangMills
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "The Casimir consumer makes derivative/limit interchange explicit and exports that generic obligation back to the YM power-series lane."
  }

data CoefficientIdentityAutomaticallyAllowsLimitDifferentiation : Set where

data ForeignDerivativeReceiptPermission : Set where

finiteDoesNotAutoInterchange :
  CoefficientIdentityAutomaticallyAllowsLimitDifferentiation → ⊥
finiteDoesNotAutoInterchange ()

foreignReceiptCannotAutoClose :
  ForeignDerivativeReceiptPermission → ⊥
foreignReceiptCannotAutoClose ()
