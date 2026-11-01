module DASHI.Physics.QuantumVacuum.CasimirResidualSummableIncrementBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SummableIncrementCauchyBidiExact as SumInc
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Residual

------------------------------------------------------------------------
-- CASIMIR RESIDUAL SUMMABLE-INCREMENT ROUTE
--
-- After matched plate/reference common-term cancellation, do not prove an
-- arbitrary two-cutoff Cauchy theorem from scratch.  It is enough to provide a
-- summable bound on successive residual cutoff increments and transport that
-- tail modulus into the imported Bishop Cauchy predicate.
------------------------------------------------------------------------

record CasimirResidualSummableIncrement : Set₁ where
  field
    residualSequence : Spine.Sequence Residual.Real
    residualAt : Nat → Spine.Carrier Residual.Real
    sequenceIsResidual : ∀ n →
      Spine._≈_ Residual.Real
        (Spine.sequenceAt Residual.Real residualSequence n)
        (residualAt n)

    rationalTailProblem : SumInc.SummableIncrementProblem
    sameLiteralCutoffTrajectory : Set

    rationalTailImpliesBishopCauchy :
      SumInc.tailBoundVanishes rationalTailProblem →
      Spine.IsCauchy Residual.Real residualSequence

    reading : String

open CasimirResidualSummableIncrement public

compileResidualRegulatorSequence :
  (C : CasimirResidualSummableIncrement) →
  Residual.ResidualRegulatorSequence
compileResidualRegulatorSequence C = record
  { Residual.residualAt = residualAt C
  ; Residual.sequence = residualSequence C
  ; Residual.sequenceIsResidual = sequenceIsResidual C
  ; Residual.cauchy =
      rationalTailImpliesBishopCauchy C
        (SumInc.tailBoundVanishes (rationalTailProblem C))
  ; Residual.reading =
      "Casimir residual sequence compiled from a summable cutoff-increment tail into Bishop Cauchy convergence."
  }

record ReverseConsumerObligations : Set₁ where
  field
    residualCutoffIncrementIdentified : Set
    incrementMajorantProved : Set
    generatedTailSummed : Set
    tailVanishesQuantitatively : Set
    rationalTailMatchesBishopMetric : Set
    sameResidualAsMatchedCasimirDifference : Set
    reading : String

open ReverseConsumerObligations public

data YangMillsIncrementEstimateAutomaticallyClosesCasimirTail : Set where

yangMillsReceiptDoesNotTransferApplications :
  YangMillsIncrementEstimateAutomaticallyClosesCasimirTail → ⊥
yangMillsReceiptDoesNotTransferApplications ()

record Status : Set where
  field
    summableIncrementRouteOwned : Bool
    cauchyCompilerReusable : Bool
    bishopLimitCompilerDownstream : Bool
    casimirIncrementEstimateClosed : Bool

    summableIncrementRouteOwnedIsTrue : summableIncrementRouteOwned ≡ true
    cauchyCompilerReusableIsTrue : cauchyCompilerReusable ≡ true
    bishopLimitCompilerDownstreamIsTrue : bishopLimitCompilerDownstream ≡ true
    casimirIncrementEstimateClosedIsFalse : casimirIncrementEstimateClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { summableIncrementRouteOwned = true
  ; cauchyCompilerReusable = true
  ; bishopLimitCompilerDownstream = true
  ; casimirIncrementEstimateClosed = false
  ; summableIncrementRouteOwnedIsTrue = refl
  ; cauchyCompilerReusableIsTrue = refl
  ; bishopLimitCompilerDownstreamIsTrue = refl
  ; casimirIncrementEstimateClosedIsFalse = refl
  }
