module DASHI.Mathematics.CrossPollination.MillenniumP9CompilerMaxCut20261014Validation where

------------------------------------------------------------------------
-- P9 COMPILER MAX-CUT VALIDATION ROOT -- 2026-10-14
------------------------------------------------------------------------

import DASHI.Mathematics.CrossPollination.MillenniumP9MaxCut20261012Validation

import DASHI.Mathematics.Complexity.VirtualStandardFiniteWindowMaterializationExact
import DASHI.Mathematics.Complexity.VirtualStandardLocalBisimulationExact

import DASHI.Mathematics.Complexity.ConcreteTapeStreamingBitSuccessfulWorkLowerExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedOwnCookSuccessfulWorkLowerExact
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionIndexABIExact

import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardSingletonLinkExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeTransitionEmbeddingExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkTransitionPreservationExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact

import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionPredicateCodeExact
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptancePredicateCodeExact
import DASHI.Mathematics.Complexity.FixedWidthPredicateDecisionTableExact
import DASHI.Mathematics.Complexity.ConcreteTapeFixedLocalKernelTablesExact

------------------------------------------------------------------------
-- CURRENT EXACT TRUST BOUNDARY
--
-- THIS MODULE DOES NOT PROVE P != NP.
--
-- NEWLY PAID ABOVE THE OCT-12 ROOT:
--
-- 1. PERSISTENT VIRTUAL / ORDINARY STANDARD REPRESENTATION
--    * every virtual `(control, absoluteHead, sparseResidual)` has a concrete
--      finite split-tape materialisation;
--    * materialised control/scanned symbol are exact;
--    * materialised left-span length is exactly the absolute head address;
--    * a virtual write is visible at the same absolute cell afterwards;
--    * a write at h leaves immediate neighbours h-1/h+1 unchanged;
--    * stay/left/right virtual transitions preserve the ordinary next scanned
--      symbol and target control locally.
--
-- 2. SAME-OBJECT STREAMING WORK + INDEX-ONLY RUNTIME ABI
--    For every successful own-Cook bit i:
--
--      i + 1
--        <= actual costed streamed evaluator work
--        <= C_D * (canonical query length + 1).
--
--    Because D=(machine,input,T) is immutable, runtime need not parse D again.
--    `GuardedCookFixedDescriptionIndexABIExact` supplies unary i as the entire
--    dynamic call payload, proves its literal length is i+1, and restates the
--    evaluator work bound directly as linear in that dynamic payload.
--
-- 3. LITERAL CODED TARGET ASSEMBLY
--    * finite same-alphabet machine fragments can be reindexed into disjoint Fin
--      state regions and summed while preserving dispatch uniqueness;
--    * cross-mode call/return/suffix rules can be appended when their dispatch
--      keys are fresh relative to resident rules;
--    * singleton links require only one resident-key freshness proof;
--    * resident transitions survive safe link insertion exactly.
--
-- 4. ACTUAL CANDIDATE SUBMACHINE SIMULATION
--    * source listed rules map rule-for-rule into the summed target;
--    * after safe links, the actual fetched source rule still determines the
--      corresponding target standard transition;
--    * `CodedFiniteStandardLinkedStructuralSimulationExact` inhabits the
--      EXISTING `StructuralStandardMachineSimulation` interface with
--      stateMap = disjoint Fin injection and symbolMap = identity;
--    * whole `standardNext` steps commute.
--
-- 5. STREAMED COOK EVALUATOR DEFUNCTIONALISATION
--    * transition placed predicates are finite `(time,column)` codes;
--    * acceptance implications are finite final-column codes;
--    * interpreting those codes reproduces the old placed-predicate lists;
--    * the only local Boolean kernels are fixed per target machine;
--    * each fixed kernel is frozen into literal finite `(row, accepted?)` data;
--    * frozen rejected-row seek is exactly equal to the old predicate-function
--      seeker;
--    * actual transition and acceptance kernels are specialized to those fixed
--      tables.
--
-- Generator runtime semantics are therefore reducible to:
--
--   unary index payload
--   + finite coordinate code
--   + fixed finite row/Bool tables
--   + Nat/index/cursor arithmetic
--   + finite clause/token output state.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. build a literal CodedFiniteStandardTM generator fragment implementing the
--    remaining first-order unary-index/table-scan/cursor operations, with exact
--    simulation and explicit compiler coefficient;
--
-- B. assemble that fragment with the ACTUAL coded polynomial candidate via the
--    proved mode-sum + safe-link machinery and add the finite opposite suffix;
--
-- C. construct concrete generator call/return runs and lift the local
--    materialisation/bisimulation lemmas to the complete exact candidate run;
--
-- D. close prefix + candidate + suffix target time to the SAME exact T used in
--    the target's own guarded Cook formula;
--
-- E. only then reuse the already-paid Cook iff / opposite endpoint path to
--    obtain SATDecisionFailure under the hypothesised polynomial SAT candidate.
--
-- Finite self-specialising/Kleene syntax remains useful for syntax-level
-- self-reference only.  Client-supplied primitive semantics is not a substitute
-- for A and is not used to launder this compiler obligation.
--
-- SOURCE STATUS: source-written/static-audited only.  No exact-head Agda kernel
-- receipt is asserted here, and no Clay-level completion is claimed.
------------------------------------------------------------------------
