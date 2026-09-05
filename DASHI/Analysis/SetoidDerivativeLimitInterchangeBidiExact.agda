module DASHI.Analysis.SetoidDerivativeLimitInterchangeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

------------------------------------------------------------------------
-- SETOID DERIVATIVE / LIMIT INTERCHANGE, BIDI
--
-- Application-neutral constructive-analysis seam for Bishop/FastCauchy-style
-- carriers.  The theorem is intentionally not postulated here.  This owner
-- identifies the one theorem family both the YM elementary-function lane and
-- the Casimir polar-coordinate lane still need, on a literal setoid real
-- backend rather than on a propositional quotient.
------------------------------------------------------------------------

record SetoidDerivativeLimitProblem : Set₁ where
  field
    R : Spine.SetoidOrderedCompleteReal
    sequences : Spine.FunctionSequenceRealization R

    Domain : Set
    approximant derivativeApproximant : Nat → Domain → Spine.Carrier R
    limitFunction derivativeLimit : Domain → Spine.Carrier R

    DerivativeAt :
      (Domain → Spine.Carrier R) →
      Domain → Spine.Carrier R → Set

    approximantDerivative : ∀ n x →
      DerivativeAt (approximant n) x (derivativeApproximant n x)

    FunctionConvergesAt : Domain → Set
    DerivativeConvergesAt : Domain → Set
    InterchangeControlAt : Domain → Set

    functionConvergence : ∀ x → FunctionConvergesAt x
    derivativeConvergence : ∀ x → DerivativeConvergesAt x

    reading : String

open SetoidDerivativeLimitProblem public

record SetoidDerivativeLimitInterchangeAuthority
    (P : SetoidDerivativeLimitProblem) : Set₁ where
  field
    interchangeControl : ∀ x → InterchangeControlAt P x
    derivativeOfLimit : ∀ x →
      DerivativeAt P (limitFunction P) x (derivativeLimit P x)

open SetoidDerivativeLimitInterchangeAuthority public

------------------------------------------------------------------------
-- Reverse proof search.  Finite differentiation and convergence of the two
-- pointwise series are not enough by themselves; the missing payment is the
-- uniform/local control that permits exchanging the analytic limit and the
-- derivative notion selected by the application.
------------------------------------------------------------------------

record ReverseSetoidInterchangeObligations : Set where
  field
    sameSetoidBackend : Set
    finiteApproximantsDifferentiable : Set
    approximantsConvergeToLiteralFunction : Set
    derivativeApproximantsConvergeToLiteralCandidate : Set
    localOrUniformInterchangeControl : Set
    sameDerivativeSemanticsAsConsumer : Set

open ReverseSetoidInterchangeObligations public

data PointwiseFunctionAndDerivativeConvergenceAutomaticallyInterchange : Set where

data PropositionalFrechetReceiptAutomaticallyIsSetoidReceipt : Set where

pointwiseDoesNotAutoInterchange :
  PointwiseFunctionAndDerivativeConvergenceAutomaticallyInterchange → ⊥
pointwiseDoesNotAutoInterchange ()

noPropositionalToSetoidLeak :
  PropositionalFrechetReceiptAutomaticallyIsSetoidReceipt → ⊥
noPropositionalToSetoidLeak ()

------------------------------------------------------------------------
-- BIDI cross-pollination ledger.
------------------------------------------------------------------------

data Lane : Set where
  yangMills casimir : Lane

record CrossPollinationEdge : Set where
  field
    source target : Lane
    theoremShapeReusable : Bool
    applicationReceiptReusable : Bool
    reading : String

open CrossPollinationEdge public

yangMillsToCasimirSetoidInterchange : CrossPollinationEdge
yangMillsToCasimirSetoidInterchange = record
  { source = yangMills
  ; target = casimir
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "The Round11 Bishop elementary-function lane and the Casimir polar lane share one setoid derivative/limit theorem shape; no physical/application receipt transfers."
  }

casimirToYangMillsSetoidInterchange : CrossPollinationEdge
casimirToYangMillsSetoidInterchange = record
  { source = casimir
  ; target = yangMills
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "The Casimir consumer exposes the missing setoid interchange hypothesis back to the generic/YM analysis lane."
  }

record Status : Set where
  field
    setoidInterchangeProblemOwned : Bool
    reverseObligationsOwned : Bool
    ymCasimirSharedTheoremShapeOwned : Bool
    concreteInterchangeTheoremClosed : Bool

    setoidInterchangeProblemOwnedIsTrue : setoidInterchangeProblemOwned ≡ true
    reverseObligationsOwnedIsTrue : reverseObligationsOwned ≡ true
    ymCasimirSharedTheoremShapeOwnedIsTrue : ymCasimirSharedTheoremShapeOwned ≡ true
    concreteInterchangeTheoremClosedIsFalse : concreteInterchangeTheoremClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { setoidInterchangeProblemOwned = true
  ; reverseObligationsOwned = true
  ; ymCasimirSharedTheoremShapeOwned = true
  ; concreteInterchangeTheoremClosed = false
  ; setoidInterchangeProblemOwnedIsTrue = refl
  ; reverseObligationsOwnedIsTrue = refl
  ; ymCasimirSharedTheoremShapeOwnedIsTrue = refl
  ; concreteInterchangeTheoremClosedIsFalse = refl
  }
