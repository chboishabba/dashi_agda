module DASHI.ComputerScience.RuntimeTernaryDecisionKernelBridgeExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.ComputerScience.ConsumerIndexedTernarySearchKernelExact as Search
import DASHI.ComputerScience.TernaryResidualBinaryDecisionRefinementExact as Runtime
import DASHI.ComputerScience.TernarySemanticDecisionRefinementExact as RuntimeRefinement
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid

------------------------------------------------------------------------
-- RUNTIME DECISIONS SHARE THE INFORMATION ORDER, NOT THE FINITE-SEARCH ENGINE
--
-- Bounded execution resolves by observing a terminal machine state.  Finite
-- candidate search resolves by finding a witness or exhausting a typed domain.
-- Those are distinct producers, but both refine information monotonically:
--
--   zer -> zer | neg | pos
--   neg -> neg
--   pos -> pos
------------------------------------------------------------------------

runtimeRefinementToGeneric :
  ∀ {before after} →
  RuntimeRefinement.DecisionRefines before after →
  Search.SearchDecisionRefines before after
runtimeRefinementToGeneric RuntimeRefinement.unresolvedStaysUnresolved =
  Search.unresolvedStaysUnresolved
runtimeRefinementToGeneric RuntimeRefinement.unresolvedBecomesNegative =
  Search.unresolvedBecomesNegative
runtimeRefinementToGeneric RuntimeRefinement.unresolvedBecomesPositive =
  Search.unresolvedBecomesPositive
runtimeRefinementToGeneric RuntimeRefinement.negativeStaysNegative =
  Search.negativeStaysNegative
runtimeRefinementToGeneric RuntimeRefinement.positiveStaysPositive =
  Search.positiveStaysPositive

------------------------------------------------------------------------
-- Same-object Euclid regressions.
------------------------------------------------------------------------

euclidRuntimeStartsUnresolved :
  Runtime.boundedDecisionTrit 0 Runtime.r0IsSix
    (Euclid.euclidInitialState 48 18) ≡ zer
euclidRuntimeStartsUnresolved = refl

euclidRuntimeResolvesPositive :
  Runtime.boundedDecisionTrit 19 Runtime.r0IsSix
    (Euclid.euclidInitialState 48 18) ≡ pos
euclidRuntimeResolvesPositive = refl

euclidRuntimeResolvesNegativeForWrongProperty :
  Runtime.boundedDecisionTrit 19 Runtime.r0IsOne
    (Euclid.euclidInitialState 48 18) ≡ neg
euclidRuntimeResolvesNegativeForWrongProperty = refl

euclidRuntimePositiveGenericRefinement : Search.SearchDecisionRefines zer pos
euclidRuntimePositiveGenericRefinement =
  runtimeRefinementToGeneric RuntimeRefinement.euclidPositiveRefinement

euclidRuntimeNegativeGenericRefinement : Search.SearchDecisionRefines zer neg
euclidRuntimeNegativeGenericRefinement =
  runtimeRefinementToGeneric RuntimeRefinement.euclidNegativeRefinement

------------------------------------------------------------------------
-- Binary quotient obstruction is the same shape.
------------------------------------------------------------------------

runtimeLegacyFalseConflatesNegativeAndUnresolved :
  Runtime.legacyBinaryTruth neg ≡ Runtime.legacyBinaryTruth zer
runtimeLegacyFalseConflatesNegativeAndUnresolved = refl

searchLegacyFalseConflatesNegativeAndUnresolved :
  Search.legacyFoundBit neg ≡ Search.legacyFoundBit zer
searchLegacyFalseConflatesNegativeAndUnresolved = refl

-- Sharing a quotient obstruction does not identify the producer semantics.
data RuntimeResolutionIsFiniteSearchExhaustion : Set where

data RuntimeDecisionIsSearchDecisionByDefinition : Set where

runtimeResolutionIsNotFiniteSearchExhaustion :
  RuntimeResolutionIsFiniteSearchExhaustion → ⊥
runtimeResolutionIsNotFiniteSearchExhaustion ()

runtimeDecisionIsNotSearchDecisionByDefinition :
  RuntimeDecisionIsSearchDecisionByDefinition → ⊥
runtimeDecisionIsNotSearchDecisionByDefinition ()

record RuntimeTernaryDecisionKernelBoundary : Set where
  constructor runtimeTernaryDecisionKernelBoundary
  field
    genericInformationOrderReused : Bool
    runtimeProducerKeptDistinct : Bool
    finiteSearchProducerKeptDistinct : Bool
    binaryFalseConflationShared : Bool
    runtimeNegativeMeansCompleteCandidateExhaustion : Bool
    radixAloneSolvesHalting : Bool

canonicalRuntimeTernaryDecisionKernelBoundary :
  RuntimeTernaryDecisionKernelBoundary
canonicalRuntimeTernaryDecisionKernelBoundary =
  runtimeTernaryDecisionKernelBoundary
    true true true true false false
