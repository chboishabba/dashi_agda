module DASHI.Statistics.Vec15BinaryDecisionDirectionalEvidenceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Statistics.Vec15Inference as Vec15
import DASHI.Statistics.BinaryTestDecisionDirectionalEvidenceExact as Binary
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- CONCRETE VEC15 ADAPTER
--
-- Vec15Inference already exposes the conventional binary decision surface
--   reject | failToReject.
-- This adapter records what that surface does NOT mean by itself.  Directional
-- scientific evidence remains an additional, separately supplied semantics.
------------------------------------------------------------------------

vec15Decision : Vec15.Decision → Binary.BinaryTestDecision
vec15Decision Vec15.reject = Binary.rejectNull
vec15Decision Vec15.failToReject = Binary.failToRejectNull

record Vec15DirectionalSemantics : Set₁ where
  constructor vec15-directional-semantics
  field
    Hypothesis : Set
    semantics : Evidence.DirectionalEvidenceSemantics Vec15.TestResult Hypothesis

    RejectSupportsPositive : Vec15.TestResult → Hypothesis → Set
    RejectSupportsNegative : Vec15.TestResult → Hypothesis → Set
    RejectUnderdetermined : Vec15.TestResult → Hypothesis → Set

    FailSupportsPositive : Vec15.TestResult → Hypothesis → Set
    FailSupportsNegative : Vec15.TestResult → Hypothesis → Set
    FailUnderdetermined : Vec15.TestResult → Hypothesis → Set

    rejectPositiveSound :
      ∀ {result hypothesis} → RejectSupportsPositive result hypothesis →
      Evidence.SupportsPositive semantics result hypothesis
    rejectNegativeSound :
      ∀ {result hypothesis} → RejectSupportsNegative result hypothesis →
      Evidence.SupportsNegative semantics result hypothesis
    rejectUnderdeterminedSound :
      ∀ {result hypothesis} → RejectUnderdetermined result hypothesis →
      Evidence.Underdetermined semantics result hypothesis

    failPositiveSound :
      ∀ {result hypothesis} → FailSupportsPositive result hypothesis →
      Evidence.SupportsPositive semantics result hypothesis
    failNegativeSound :
      ∀ {result hypothesis} → FailSupportsNegative result hypothesis →
      Evidence.SupportsNegative semantics result hypothesis
    failUnderdeterminedSound :
      ∀ {result hypothesis} → FailUnderdetermined result hypothesis →
      Evidence.Underdetermined semantics result hypothesis

open Vec15DirectionalSemantics public

------------------------------------------------------------------------
-- The concrete result only determines the binary decision.  There is no generic
-- constructor from Vec15.failToReject to SupportsNegative or SupportsPositive.
------------------------------------------------------------------------

record Vec15FailToRejectWitness (result : Vec15.TestResult) : Set where
  constructor vec15-fail-to-reject-witness
  field
    isFailToReject : Vec15.TestResult.decision result ≡ Vec15.failToReject

open Vec15FailToRejectWitness public

record Vec15RejectWitness (result : Vec15.TestResult) : Set where
  constructor vec15-reject-witness
  field
    isReject : Vec15.TestResult.decision result ≡ Vec15.reject

open Vec15RejectWitness public

data Vec15FailToRejectMeansNegativeEvidencePermission : Set where

data Vec15FailToRejectMeansPositiveEvidencePermission : Set where

data Vec15RejectMeansScientificAlternativePermission : Set where

vec15FailToRejectDoesNotMeanNegativeEvidence :
  Vec15FailToRejectMeansNegativeEvidencePermission → ⊥
vec15FailToRejectDoesNotMeanNegativeEvidence ()

vec15FailToRejectDoesNotMeanPositiveEvidence :
  Vec15FailToRejectMeansPositiveEvidencePermission → ⊥
vec15FailToRejectDoesNotMeanPositiveEvidence ()

vec15RejectDoesNotByItselfProveScientificAlternative :
  Vec15RejectMeansScientificAlternativePermission → ⊥
vec15RejectDoesNotByItselfProveScientificAlternative ()

------------------------------------------------------------------------
-- Regression receipt over the legacy statistics surface.
------------------------------------------------------------------------

record Vec15BinaryDecisionDirectionalBoundary : Set where
  constructor vec15-binary-decision-directional-boundary
  field
    vec15DecisionSurfaceRemainsBinary : Bool
    vec15FailToRejectIsGenericNegativeEvidence : Bool
    vec15FailToRejectIsGenericPositiveEvidence : Bool
    vec15RejectAutomaticallyProvesScientificAlternative : Bool
    directionalInterpretationRequiresSeparateSemantics : Bool

canonicalVec15BinaryDecisionDirectionalBoundary :
  Vec15BinaryDecisionDirectionalBoundary
canonicalVec15BinaryDecisionDirectionalBoundary =
  vec15-binary-decision-directional-boundary true false false false true
