module DASHI.Interop.DirectionalEvidenceProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Trit as Trit
import DASHI.Statistics.DirectionalEvidenceTritExact as Directional
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- DIRECTIONAL EVIDENCE -> REOPENABLE PROOF-SEARCH STATUS
--
-- The centre trit is the important bridge: underdetermined evidence keeps the
-- hypothesis reopenable. It is not silently compiled into refutation.
------------------------------------------------------------------------

record DirectionalForestBridge
    (Result Hypothesis : Set)
    (semantics : Directional.DirectionalInferenceSemantics Result Hypothesis)
    (forestSemantics : Forest.HypothesisSemantics Hypothesis) : Set₁ where
  constructor directionalForestBridge
  field
    negativeEvidenceRefutes :
      (result : Result) (hypothesis : Hypothesis) →
      Directional.SupportsNegative semantics result hypothesis →
      Forest.Refutation forestSemantics hypothesis
    unresolvedReason : Forest.DormancyReason
    bridgeReference : String
open DirectionalForestBridge public

underdeterminedStatus : Forest.HypothesisStatus
underdeterminedStatus = Forest.reopenable Forest.ambiguityUnresolved

underdeterminedRemainsReopenable :
  underdeterminedStatus ≡ Forest.reopenable Forest.ambiguityUnresolved
underdeterminedRemainsReopenable = refl

record DirectionalProofSearchBoundary : Set where
  constructor directionalProofSearchBoundary
  field
    underdeterminedEvidenceRefutesHypothesis : Bool
    negativeEvidenceMayRefuteWithBridgeWitness : Bool
    inactiveHypothesisAutomaticallyMeansNegativeEvidence : Bool
    centreTritRoutesToReopenableResidual : Bool

canonicalDirectionalProofSearchBoundary : DirectionalProofSearchBoundary
canonicalDirectionalProofSearchBoundary =
  directionalProofSearchBoundary false true false true

existingForestBoundary : Forest.ReopenableHypothesisBoundary
existingForestBoundary = Forest.canonicalReopenableHypothesisBoundary
