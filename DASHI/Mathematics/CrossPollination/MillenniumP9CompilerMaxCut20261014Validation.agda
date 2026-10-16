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
open import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedRunSimulationExact
  using (simulateLinkedExactRun; simulateCodedCandidateExecution; appendLinkedCandidatePhase)
open import DASHI.Mathematics.Complexity.CodedFiniteStandardReturnLinkFreshnessExact
  using (residentCandidateRuleBlocksReturnLink)

import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionPredicateCodeExact
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptancePredicateCodeExact
import DASHI.Mathematics.Complexity.FixedWidthPredicateDecisionTableExact
import DASHI.Mathematics.Complexity.ConcreteTapeFixedLocalKernelTablesExact

-- Recent XOR-grid work is consumed only through a locally reproved complexity
-- microcode boundary.  No IIT numerical quantity or sibling-branch theorem is
-- imported as complexity-theoretic authority.
open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitFalseBorrow
    ; countdownBitTrueBorrow
    ; canonicalXORCountdownBoundary
    )

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
--    * whole `standardNext` steps commute;
--    * `CodedFiniteStandardLinkedRunSimulationExact` lifts this pointwise result
--      to exact whole runs with IDENTICAL step count and specializes it to the
--      actual `CodedStandardPolynomialDecider.execution` witness;
--    * exact prefix ; candidate ; suffix runs compose with the literal additive
--      phase clock, so the candidate middle phase is no longer a separate C-wall;
--    * safe return links CANNOT share a dispatch key with a resident candidate
--      rule.  Hence a T-step `finish` that still has an outgoing resident rule
--      cannot be used as a direct return boundary without a clock/phase wrapper
--      or a halting-normal-form transformation.
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
-- 6. XOR / BORROW CLOCK MICROCODE CROSS-POLLINATION
--    * the recent XOR-grid result is used only as design guidance; all Boolean
--      facts needed here are reproved on the complexity branch;
--    * one binary countdown cell has data update `bit XOR borrowIn`;
--    * XOR is coordinate-recoverable in either input, so this part of the local
--      timer microcode is information-preserving;
--    * the outgoing borrow is `(NOT bit) AND borrowIn` and does NOT factor
--      through XOR output: `(false,true)` and `(true,false)` have equal XOR
--      output but different outgoing borrow;
--    * therefore XOR/parity alone is not an exact-T clock and IIT phi is not a
--      complexity lower bound.  A literal timer must carry bit + borrow/carry
--      state and compile both into finite tape/rule-table execution.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. build a literal CodedFiniteStandardTM generator fragment implementing the
--    remaining first-order unary-index/table-scan/cursor operations, with exact
--    simulation and explicit compiler coefficient;
--
-- B. compile a compact tape counter from the now-explicit binary countdown
--    microcode (XOR data update + separate borrow/carry propagation), and prove
--    that it emits the unique handoff pulse at the selected exact budget;
--
-- C. assemble generator + counter + ACTUAL coded polynomial candidate + finite
--    opposite suffix using the paid mode-sum/link machinery.  The counter must
--    transfer control into a fresh/quiescent phase namespace; no direct link may
--    override a resident candidate dispatch key;
--
-- D. construct generator/counter/return/suffix exact runs.  Candidate middle
--    execution and generic run composition are already paid;
--
-- E. choose/close one FINAL exact target budget T* that pays generator + timer +
--    candidate + suffix and is the SAME T* encoded in that target's guarded Cook
--    formula.  The wrapper is not required to fit inside the candidate's old T;
--    its overhead must be charged honestly into the final fixed-point budget;
--
-- F. only then reuse the already-paid Cook iff / opposite endpoint path to
--    obtain SATDecisionFailure under the hypothesised polynomial SAT candidate.
--
-- SOURCE STATUS: source-written/static-audited only.  No exact-head Agda kernel
-- receipt is asserted here, and no Clay-level completion is claimed.
------------------------------------------------------------------------
