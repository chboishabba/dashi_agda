module DASHI.Interop.DirectionalEvidenceProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- DIRECTIONAL EVIDENCE / PROOF-SEARCH BRIDGE
--
-- Statistical or experimental non-support is not proof-search refutation.
-- The unresolved balanced-ternary centre maps naturally to a reopenable
-- hypothesis state, while actual refutation remains proof-bearing in the
-- canonical hypothesis forest.
------------------------------------------------------------------------

record EvidenceToHypothesisStatus
    (Result Hypothesis : Set)
    (semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis)
    (forestSemantics : Forest.HypothesisSemantics Hypothesis) : Set₁ where
  constructor evidence-to-hypothesis-status
  field
    result : Result
    hypothesis : Hypothesis

    positiveDisposition :
      Evidence.DirectionalEvidenceDisposition semantics result hypothesis pos →
      Forest.HypothesisStatus

    unresolvedDisposition :
      Evidence.DirectionalEvidenceDisposition semantics result hypothesis zer →
      Forest.HypothesisStatus

    negativeRefutation :
      Evidence.DirectionalEvidenceDisposition semantics result hypothesis neg →
      Forest.Refutation forestSemantics hypothesis

open EvidenceToHypothesisStatus public

------------------------------------------------------------------------
-- Canonical unresolved route: underdetermination remains reopenable rather than
-- becoming refuted merely because the positive route failed.
------------------------------------------------------------------------

unresolvedToReopenable :
  ∀ {Result Hypothesis : Set}
    {semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis}
    {result : Result} {hypothesis : Hypothesis} →
  Evidence.DirectionalEvidenceDisposition semantics result hypothesis zer →
  Forest.HypothesisStatus
unresolvedToReopenable _ =
  Forest.reopenable Forest.ambiguityUnresolved

------------------------------------------------------------------------
-- Refutation remains a second-stage compiler.  A negative evidence disposition
-- is not definitionally a refutation: applications must provide the theorem
-- connecting their negative statistical claim to the hypothesis semantics.
------------------------------------------------------------------------

record NegativeEvidenceRefutationReceipt
    {Result Hypothesis : Set}
    (semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis)
    (forestSemantics : Forest.HypothesisSemantics Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor negative-evidence-refutation-receipt
  field
    negativeDisposition :
      Evidence.DirectionalEvidenceDisposition semantics result hypothesis neg
    refutationWitness : Forest.Refutation forestSemantics hypothesis

open NegativeEvidenceRefutationReceipt public

refuteFromNegativeReceipt :
  ∀ {Result Hypothesis : Set}
    {semantics : Evidence.DirectionalEvidenceSemantics Result Hypothesis}
    {forestSemantics : Forest.HypothesisSemantics Hypothesis}
    {result : Result} {hypothesis : Hypothesis} →
  NegativeEvidenceRefutationReceipt
    semantics forestSemantics result hypothesis →
  Forest.HypothesisTransition
    forestSemantics hypothesis Forest.active Forest.refuted
refuteFromNegativeReceipt receipt =
  Forest.refuteActive (refutationWitness receipt)

------------------------------------------------------------------------
-- Firewalls connecting the statistics lesson to the generic proof-search law.
------------------------------------------------------------------------

data FailedPositiveProofSearchMeansRefutationPermission : Set where

data UnderdeterminedEvidenceMeansRefutationPermission : Set where

data NegativeEvidenceAutomaticallyMeansRefutationPermission : Set where

failedPositiveProofSearchDoesNotMeanRefutation :
  FailedPositiveProofSearchMeansRefutationPermission → ⊥
failedPositiveProofSearchDoesNotMeanRefutation ()

underdeterminedEvidenceDoesNotMeanRefutation :
  UnderdeterminedEvidenceMeansRefutationPermission → ⊥
underdeterminedEvidenceDoesNotMeanRefutation ()

negativeEvidenceStillNeedsRefutationBridge :
  NegativeEvidenceAutomaticallyMeansRefutationPermission → ⊥
negativeEvidenceStillNeedsRefutationBridge ()

record DirectionalEvidenceProofSearchBoundary : Set where
  constructor directional-evidence-proof-search-boundary
  field
    failedPositiveRouteIsCounterproof : Bool
    unresolvedEvidenceRemainsReopenable : Bool
    negativeEvidenceIsDefinitionallyRefutation : Bool
    refutationRequiresHypothesisSemanticWitness : Bool

canonicalDirectionalEvidenceProofSearchBoundary :
  DirectionalEvidenceProofSearchBoundary
canonicalDirectionalEvidenceProofSearchBoundary =
  directional-evidence-proof-search-boundary false true false true
