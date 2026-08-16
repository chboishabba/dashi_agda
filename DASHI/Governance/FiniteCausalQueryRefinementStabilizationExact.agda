module DASHI.Governance.FiniteCausalQueryRefinementStabilizationExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Reuses the exact finite ranked stabilization producer ported from PR #548.
-- Governance interpretation: if every unresolved observation-relevant split
-- strictly raises a bounded refinement rank, iterative causal/query refinement
-- must eventually reach a stable code.  "Increase causal resolution" therefore
-- does not mean "add detail forever"; it means refine until the declared query
-- language no longer forces an additional distinction.
--
-- No political or empirical claim is encoded by this finite theorem.  A case
-- must supply its own rank, refinement rule and meaning of query completeness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Core.Prelude

import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked

record CausalQueryRefinementSystem : Set₁ where
  constructor causalQueryRefinementSystem
  field
    process : Ranked.RankedRefinementProcess
    initialCode : Ranked.Code process
    QueryComplete : Ranked.Code process → Set
    stableIsQueryComplete :
      (code : Ranked.Code process) →
      code ≡ Ranked.advance process code →
      QueryComplete code

open CausalQueryRefinementSystem public

record StableQueryResolution
  (S : CausalQueryRefinementSystem) : Set where
  constructor stableQueryResolution
  field
    depth : Nat
    depthBound : depth ≤ Ranked.rankBound (process S)
    stableCode : Ranked.Code (process S)
    codeExact :
      stableCode ≡ Ranked.iterate (process S) depth (initialCode S)
    stable :
      stableCode ≡ Ranked.advance (process S) stableCode
    queryComplete : QueryComplete S stableCode

open StableQueryResolution public

finiteRankedQueryRefinementStabilizes :
  (S : CausalQueryRefinementSystem) →
  StableQueryResolution S
finiteRankedQueryRefinementStabilizes S
  with Ranked.rankedRefinementStabilizes (process S) (initialCode S)
... | Ranked.stabilizationWitness depth depth≤bound stable =
  stableQueryResolution
    depth
    depth≤bound
    (Ranked.iterate (process S) depth (initialCode S))
    refl
    stable
    (stableIsQueryComplete S _ stable)

------------------------------------------------------------------------
-- Boundary: bounded-rank stabilization is conditional on the supplied process.
------------------------------------------------------------------------

record FiniteCausalQueryRefinementBoundary : Set where
  constructor finiteCausalQueryRefinementBoundary
  field
    moreDetailAlwaysImprovesInquiry : Bool
    boundedStrictRefinementEventuallyStabilizes : Bool
    stableCodeMeansUniversalTruth : Bool
    queryCompletenessIsRelativeToDeclaredLanguage : Bool
    empiricalRankMustBeSuppliedByCase : Bool

canonicalFiniteCausalQueryRefinementBoundary :
  FiniteCausalQueryRefinementBoundary
canonicalFiniteCausalQueryRefinementBoundary =
  finiteCausalQueryRefinementBoundary
    false
    true
    false
    true
    true
