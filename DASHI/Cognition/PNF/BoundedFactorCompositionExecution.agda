module DASHI.Cognition.PNF.BoundedFactorCompositionExecution where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.ProofRelevantFactorDerivations

------------------------------------------------------------------------
-- Migration 082 execution contract.
--
-- Retained composition candidates are bounded before materialisation.  If the
-- structural pair carrier is larger than the retained budget, runtime records an
-- overflow receipt.  Overflow is execution evidence only; it cannot itself
-- reject a semantic relation or license a derived proposition.
------------------------------------------------------------------------

record CompositionEnumeration : Set where
  constructor compositionEnumeration
  field
    possiblePairCount : Nat
    retainedPairCount : Nat
    retainedPairLimit : Nat
    retainedWithinLimit : retainedPairCount ≤ᶜ retainedPairLimit

open CompositionEnumeration public

data CompositionOverflowState : Set where
  completeWithinBudget overflowObserved : CompositionOverflowState

record CompositionOverflowReceipt : Set where
  constructor compositionOverflowReceipt
  field
    enumeration : CompositionEnumeration
    overflowState : CompositionOverflowState

open CompositionOverflowReceipt public

data OverflowSemanticAuthority : Set where
  executionEvidenceOnly : OverflowSemanticAuthority

-- There is intentionally no constructor converting overflow execution evidence
-- into CompositionPermission explicitDomainRuleAuthority.
overflowCannotLicenseComposition :
  OverflowSemanticAuthority →
  CompositionPermission explicitDomainRuleAuthority →
  CompositionPermission explicitDomainRuleAuthority
overflowCannotLicenseComposition executionEvidenceOnly permission = permission

record BoundedCompositionExecutionBoundary : Set where
  constructor boundedCompositionExecutionBoundary
  field
    overflowAuthority : OverflowSemanticAuthority

open BoundedCompositionExecutionBoundary public

canonicalBoundedCompositionExecutionBoundary : BoundedCompositionExecutionBoundary
canonicalBoundedCompositionExecutionBoundary =
  boundedCompositionExecutionBoundary executionEvidenceOnly
