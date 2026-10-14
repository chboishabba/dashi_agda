module DASHI.Mathematics.CrossPollination.MillenniumP9CompilerMaxCut20261014Validation where

------------------------------------------------------------------------
-- P9 COMPILER MAX-CUT VALIDATION ROOT -- 2026-10-14
--
-- Extends the Oct-12 validation surface with the concrete compiler work that is
-- now actually paid.  This module is deliberately import-only plus a trust
-- boundary: theorem authority remains in the production owners below.
------------------------------------------------------------------------

import DASHI.Mathematics.CrossPollination.MillenniumP9MaxCut20261012Validation

-- Persistent virtual tape -> finite conventional tape observations.
import DASHI.Mathematics.Complexity.VirtualStandardFiniteWindowMaterializationExact
import DASHI.Mathematics.Complexity.VirtualStandardLocalBisimulationExact

-- Intrinsic same-object indexed-access lower/upper work sandwich.
import DASHI.Mathematics.Complexity.ConcreteTapeStreamingBitSuccessfulWorkLowerExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedOwnCookSuccessfulWorkLowerExact

-- Literal finite coded-machine composition and safe cross-mode links.
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardSingletonLinkExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeTransitionEmbeddingExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkTransitionPreservationExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact

-- Defunctionalized Cook predicate streams and fixed local kernels.
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
-- 2. SAME-OBJECT STREAMING WORK SANDWICH
--    For every successful own-Cook bit i:
--
--      i + 1
--        <= actual costed streamed evaluator work
--        <= C_D * (canonical query length + 1).
--
--    Thus indexed access has an intrinsic linear lower endpoint; the future
--    standard-TM compiler may pay a fixed/polynomial simulation coefficient but
--    cannot pretend the semantic evaluator itself has zero/sublinear work.
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
--    * `CodedFiniteStandardLinkedStructuralSimulationExact` therefore inhabits
--      the EXISTING `StructuralStandardMachineSimulation` interface with
--      stateMap = disjoint Fin injection and symbolMap = identity;
--    * whole `standardNext` steps commute.  The resource-closing candidate
--      middle phase no longer needs an arbitrary meta-level embed for this
--      compiler architecture.
--
-- 5. STREAMED COOK EVALUATOR DEFUNCTIONALISATION
--    * transition placed predicates are finite `(time,column)` codes;
--    * interpreting those codes reproduces `allGlobalTransitionPredicates`
--      exactly;
--    * acceptance implications are finite final-column codes with exact
--      interpretation;
--    * the only remaining local Boolean kernels are fixed per target machine;
--    * each such kernel is frozen into literal finite `(row, accepted?)` data;
--    * rejected-row streaming over that finite data is exactly equal to the old
--      predicate-function seeker;
--    * the actual transition and acceptance kernels are specialized to those
--      frozen tables.
--
-- Therefore the generator runtime no longer requires arbitrary higher-order
-- functions.  Its semantic data are now reducible to:
--
--   finite coordinate code
--   + fixed finite row/Bool tables
--   + Nat/index/cursor arithmetic
--   + finite clause/token output state.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. build a literal CodedFiniteStandardTM generator fragment implementing the
--    remaining first-order Nat/index/table-scan/cursor operations, with an exact
--    simulation theorem and explicit compiler coefficient;
--
-- B. assemble that fragment with the ACTUAL coded polynomial candidate via the
--    proved mode-sum + safe-link machinery and add the finite opposite suffix;
--
-- C. construct the concrete generator call/return runs needed by the persistent
--    virtual candidate execution and lift the local materialisation/bisimulation
--    lemmas to the complete exact candidate run;
--
-- D. close prefix + candidate + suffix target time to the SAME exact T used in
--    the target's own guarded Cook formula;
--
-- E. only then reuse the already-paid Cook iff / opposite endpoint path to
--    obtain SATDecisionFailure under the hypothesised polynomial SAT candidate.
--
-- The old finite self-specialising/Kleene code remains useful only for syntax
-- self-reference.  Its client-supplied primitive semantics is NOT a substitute
-- for A: it does not compile these first-order operations into standard-TM
-- steps, so no interpreter laundering is used here.
--
-- SOURCE STATUS: source-written/static-audited only.  No exact-head Agda kernel
-- receipt is asserted by this validation root, and no Clay-level completion is
-- claimed.
------------------------------------------------------------------------
