module DASHI.Environment.HybridTraceSafetyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Round 2 introduced the hybrid flow/jump carrier.  This module proves the
-- actual finite-trace safety theorem: if every declared flow/jump command
-- preserves a safety predicate, every finite mixed trace preserves it.
--
-- REFERENCE / MOTIVATION
--
-- Rajeev Alur, Costas Courcoubetis, Thomas A. Henzinger, Pei-Hsin Ho,
-- "Hybrid Automata: An Algorithmic Approach to the Specification and
-- Verification of Hybrid Systems", Hybrid Systems I, LNCS 736, 1993.
--
-- The source motivates hybrid execution/reachability.  This theorem is only
-- finite trace induction over the existing LES command semantics; it does not
-- claim decidability of unrestricted hybrid reachability.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.GenericFuturePartitionRefinementExact as Future
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Hybrid

runHybrid :
  ∀ {Mode Continuous DiscreteAction} →
  Hybrid.HybridSystem Mode Continuous DiscreteAction →
  List (Hybrid.HybridCommand Mode Continuous DiscreteAction) →
  Hybrid.HybridState Mode Continuous →
  Hybrid.HybridState Mode Continuous
runHybrid system = Future.run (Hybrid.hybridStep system)

hybridTracePreservesSafe :
  ∀ {Mode Continuous DiscreteAction}
    {system : Hybrid.HybridSystem Mode Continuous DiscreteAction}
    {Safe : Hybrid.HybridState Mode Continuous → Set} →
  Hybrid.HybridSafetyWitness system Safe →
  (commands : List (Hybrid.HybridCommand Mode Continuous DiscreteAction)) →
  (state : Hybrid.HybridState Mode Continuous) →
  Safe state →
  Safe (runHybrid system commands state)
hybridTracePreservesSafe witness [] state safe = safe
hybridTracePreservesSafe witness (command ∷ rest) state safe =
  hybridTracePreservesSafe witness rest
    (Hybrid.hybridStep _ command state)
    (Hybrid.stepPreservesSafe witness command state safe)

record HybridTraceBoundary : Set where
  constructor hybridTraceBoundary
  field
    oneStepInvariantLiftsToFiniteMixedTrace : Bool
    theoremCoversDeclaredFlowAndJumpCommands : Bool
    theoremDoesNotSolveContinuousReachability : Bool
    theoremDoesNotConstructPhysicalFlowLaw : Bool

canonicalHybridTraceBoundary : HybridTraceBoundary
canonicalHybridTraceBoundary =
  hybridTraceBoundary true true true true
