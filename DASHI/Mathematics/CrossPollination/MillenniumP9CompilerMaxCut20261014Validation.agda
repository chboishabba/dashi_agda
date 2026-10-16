module DASHI.Mathematics.CrossPollination.MillenniumP9CompilerMaxCut20261014Validation where

------------------------------------------------------------------------
-- P9 COMPILER MAX-CUT VALIDATION ROOT -- refreshed 2026-10-16
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

-- XOR-grid cross-pollination is bounded to local compiler structure.  The
-- complexity branch reproves all needed Boolean facts locally; no IIT numerical
-- quantity or sibling-branch theorem is imported as lower-bound authority.
open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitFalseBorrow
    ; countdownBitTrueBorrow
    ; countdownBitsNoBorrow
    ; decrementOne
    ; decrementTwo
    ; decrementFour
    ; canonicalXORCountdownBoundary
    )
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentValidation

-- Exact finite-control phase wrapper for candidate endpoint quiescence.
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardPhaseShiftSimulationExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedCandidateExactPhaseBoundaryExact

-- Exact static-size audit of that wrapper.  Quiescence is paid, but the wrapper
-- is not treated as free in the self-description fixed point.
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeValidation

-- First literal generator microprogram: unary index cursor as finite TM syntax.
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact

------------------------------------------------------------------------
-- CURRENT EXACT TRUST BOUNDARY
--
-- THIS MODULE DOES NOT PROVE P != NP.
--
-- PAID ABOVE THE OCT-12 ROOT:
--
-- 1. PERSISTENT VIRTUAL / ORDINARY STANDARD REPRESENTATION
--    * virtual `(control, absoluteHead, sparseResidual)` materialises to the
--      ordinary split-tape carrier;
--    * local stay/left/right semantics agree exactly;
--    * one write changes only the written location and sparse lookup is charged.
--
-- 2. SAME-OBJECT STREAMING WORK + INDEX-ONLY ABI
--    * successful own-Cook bit access has the intrinsic lower bound i+1;
--    * the actual costed streamed evaluator has a fixed-description degree-one
--      upper envelope;
--    * runtime dynamic input is only unary i; `(machine,input,T)` is static.
--
-- 3. LITERAL CODED TARGET ASSEMBLY
--    * disjoint finite mode sums preserve dispatch uniqueness;
--    * fresh singleton call/return/suffix rules can be appended safely;
--    * resident transitions survive safe-link extension.
--
-- 4. ACTUAL CANDIDATE SUBMACHINE SIMULATION
--    * source rules map rule-for-rule into the linked target;
--    * whole source runs lift edge-for-edge with identical step count;
--    * prefix ; candidate ; suffix exact runs compose additively.
--
-- 5. STREAMED COOK EVALUATOR DEFUNCTIONALISATION
--    * transition predicates are finite `(time,column)` codes;
--    * acceptance predicates are finite column codes;
--    * fixed local Boolean kernels are frozen into finite row/Bool tables;
--    * runtime no longer requires an arbitrary higher-order predicate call.
--
-- 6. EXACT-T CANDIDATE PHASE BOUNDARY -- OPERATIONALLY PAID
--    `CodedFiniteStandardExactPhaseLiftExact` expands finite control to
--
--        Fin (|Q| * (T+1))
--
--    and copies each source rule at each phase k<T.  There is no resident rule
--    at terminal phase T.  `CodedFiniteStandardExactPhaseRunExact` transports an
--    exact source T-run to an exact phase-lifted T-run, and
--    `PNotEqualsNPCodedCandidateExactPhaseBoundaryExact` specializes this to the
--    actual coded polynomial candidate.  Acceptance is preserved and the final
--    dispatch is quiescent.
--
-- 7. PHASE-LIFT SIZE FEEDBACK -- NOW EXPLICIT
--    `CodedFiniteStandardExactPhaseSizeExact` proves exactly:
--
--        phase states = |Q| * (T+1)
--        phase rules  = T * |R|.
--
--    Therefore the phase lift is a correct endpoint compiler but has O(T)
--    static program-text growth.  In a self-Cook construction that code belongs
--    to the described target, so the final resource fixed point must charge it.
--    The compact XOR/borrow runtime-counter route remains a lawful competing
--    implementation: it trades execution overhead for smaller static code.
--
-- 8. XOR / RIPPLE-COUNTDOWN CROSS-POLLINATION -- BOUNDED AND ATTRIBUTION-SAFE
--    * binary countdown data update is `bit XOR borrowIn`;
--    * XOR is recoverable in either coordinate;
--    * borrow is a separate nonlinear coordinate and provably does not factor
--      through XOR output alone;
--    * finite little-endian ripple countdown semantics are executable;
--    * a literal three-rule decrement fragment with quiescent resolved/underflow
--      controls exists;
--    * none of this identifies IIT phi with complexity hardness.
--
-- 9. FIRST LITERAL GENERATOR MICROPROGRAM -- UNARY CURSOR PAID
--    `CodedFiniteUnaryCursorExact` compiles unary index traversal to actual
--    finite standard-TM syntax.  Each `more` is one edge, exact phase control
--    makes the terminal cursor phase quiescent, and `stop` is a fresh dispatch
--    key at every phase.  Runtime unary-index traversal is therefore no longer
--    an Agda Nat recursion.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. STATIC ANSWER-STREAM / OUTPUT MICROPROGRAM
--    Compile the fixed-description Cook answer stream into literal finite
--    stop/output rules over the paid unary cursor, then prove exact agreement
--    with the already-costed streamed evaluator.  Coordinate/table/token-cursor
--    helpers remain to be lowered only where the static lookup compiler cannot
--    eliminate them at compile time.
--
-- B. REPRESENTATION PARETO CUT FOR EXACT-T HANDOFF
--    Compare two honest target architectures on the SAME described machine:
--      (i) finite-control phase lift: zero runtime timer, O(T) static rules;
--     (ii) compact tape/ripple timer: bounded static rules, charged runtime work.
--    Do not choose by convenience.  Choose the route that can actually close
--    the self-description / same-Cook-budget inequality after code size is fed
--    back into the target formula.
--
-- C. TARGET ASSEMBLY + SURROUNDING RUNS
--    Sum generator + chosen candidate clock representation + opposite suffix;
--    attach call/return/suffix links; construct exact generator and suffix runs.
--    Candidate execution and generic run composition are already paid.
--
-- D. SAME-T SELF-DESCRIPTION CLOSURE
--    Choose one final exact target budget T* paying all generator/clock/candidate/
--    suffix work AND describing that same final target code in the guarded Cook
--    formula.  This fixed-point/resource inequality is now the principal live
--    mathematical wall.
--
-- E. TERMINAL CONTRADICTION + BARRIER AUDIT
--    Only after A-D, reuse the existing Cook iff/opposite endpoint route to obtain
--    `SATDecisionFailure` and the existing same-model SATNotInP -> PNotEqualsNP
--    compiler.  A successful closure must then be audited explicitly against
--    relativisation/algebrisation/natural-proof barriers rather than assuming
--    ordinary diagonal syntax escapes them.
--
-- SOURCE STATUS: source-written/static-audited only.  No exact-head Agda kernel
-- receipt is asserted here, and no Clay-level completion is claimed.
------------------------------------------------------------------------
