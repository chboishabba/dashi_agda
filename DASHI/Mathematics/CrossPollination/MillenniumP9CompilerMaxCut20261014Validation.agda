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

-- The old XOR/borrow timer exploration remains a valid local microcode donor,
-- but is no longer required for the exact-T candidate return boundary.
open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitFalseBorrow
    ; countdownBitTrueBorrow
    ; canonicalXORCountdownBoundary
    )

-- Exact finite-control phase wrapper replacing the old direct-return/tape-timer
-- blocker on the Clay-critical path.
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardPhaseShiftSimulationExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedCandidateExactPhaseBoundaryExact

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
-- 6. EXACT-T CANDIDATE PHASE BOUNDARY -- NOW PAID
--
--    `CodedFiniteStandardExactPhaseLiftExact` compiles a source code with fixed
--    budget T into the literal finite state space
--
--        Fin (|Q| * (T+1)).
--
--    Every source rule is copied at each elapsed phase k<T and advances k->k+1.
--    There is NO resident rule at phase T for any source state or scanned symbol.
--    The terminal standard transition is therefore literally `nothing`.
--
--    `CodedFiniteStandardPhaseShiftSimulationExact` embeds the T-phase wrapper
--    into phases 1..T+1 of the (T+1)-phase wrapper with one edge preserved as
--    one edge.
--
--    `CodedFiniteStandardExactPhaseRunExact` then proves by induction:
--
--        source exact T-step run
--          -> phase-lifted exact T-step run
--
--    with the same tape evolution and terminal elapsed phase exactly T.
--
--    `PNotEqualsNPCodedCandidateExactPhaseBoundaryExact` specializes this to the
--    actual `CodedStandardPolynomialDecider.execution` witness.  Hence the
--    candidate's polynomial step count is unchanged, its acceptance status is
--    preserved propositionally, and its exact endpoint is quiescent.
--
--    CONSEQUENCE: the old direct-return obstruction and the proposed runtime
--    tape timer are no longer Clay-critical blockers.  A return/opposite link
--    can leave the finite-control terminal slice without overriding a resident
--    candidate transition.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. GENERATOR MICROPROGRAM
--    Build a literal `CodedFiniteStandardTM` fragment implementing the remaining
--    first-order fixed-description unary-index / coordinate / finite-table /
--    token-cursor operations.  Prove exact agreement with the already-costed
--    streamed own-Cook evaluator and expose the compiler coefficient.
--
-- B. PHASED TARGET ASSEMBLY
--    Sum generator + EXACT PHASE-LIFTED candidate + opposite suffix and attach
--    generator/candidate/return/suffix links.  Candidate T-boundary freshness is
--    now supplied constructively by the phase wrapper.
--
-- C. SURROUNDING EXACT RUNS
--    Construct the generator/call and return/opposite suffix runs.  Candidate
--    middle execution, exact phase boundary, and generic run composition are paid.
--
-- D. SAME-T SELF-CLOCK CLOSURE
--    Choose one final exact target budget T* paying generator + phase-lifted
--    candidate + suffix, where the SAME T* occurs in that target's guarded Cook
--    formula.  This is now the principal mathematical fixed-point/resource wall.
--
-- E. TERMINAL CONTRADICTION + BARRIER AUDIT
--    Only after A-D, reuse the existing Cook iff/opposite endpoint route to obtain
--    `SATDecisionFailure` and the existing same-model SATNotInP -> PNotEqualsNP
--    compiler.  A successful closure must then be audited explicitly against
--    relativisation/algebrisation/natural-proof barriers rather than assuming
--    that ordinary diagonal syntax escapes them.
--
-- SOURCE STATUS: source-written/static-audited only.  No exact-head Agda kernel
-- receipt is asserted here, and no Clay-level completion is claimed.
------------------------------------------------------------------------
