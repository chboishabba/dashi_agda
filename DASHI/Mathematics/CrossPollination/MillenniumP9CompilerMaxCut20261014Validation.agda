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
import DASHI.Mathematics.Complexity.ConcreteTapeFixedLocalKernelTablesExact

import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkExtensionExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedStructuralSimulationExact
open import DASHI.Mathematics.Complexity.CodedFiniteStandardLinkedRunSimulationExact
  using (simulateLinkedExactRun; simulateCodedCandidateExecution; appendLinkedCandidatePhase)

import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardPhaseShiftSimulationExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseRunExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedCandidateExactPhaseBoundaryExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeValidation

import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupTransitionExact
import DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableGeneratorExact
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinStateWidthLowerExact
import DASHI.Mathematics.Complexity.GuardedCookFiniteBitTableSelfCodeNoGoExact

-- Runtime/Cook representation separation is now constructive rather than a socket.
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact
import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateBridgeExact
import DASHI.Mathematics.Complexity.StandardBlankTailBisimulationValidation
import DASHI.Mathematics.Complexity.GuardedStandardStartBlankTailExact
import DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerValidation

-- Behavioural quotation/interpreter path is now concrete through typed fidelity.
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityValidation
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact
import DASHI.Mathematics.Complexity.PNotEqualsNPLiteralSelfCodeGrowthNoGoExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact

-- First literal compiler primitives for the self-delimiting/raw interpreter.
-- Unary field scanning/equality stay on their natural unary representation;
-- XOR is not forced into equality because doing so would add pairing/routing work.
import DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerExact
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureValidation

-- XOR-grid cross-pollination remains bounded to local compiler structure.  All
-- Boolean facts needed by the complexity lane are reproved locally; no IIT phi
-- value or sibling-branch theorem is imported as lower-bound authority.
open import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeValidation
  using
    ( xorRecoverLeft
    ; xorRecoverRight
    ; sameXorOutputDifferentBorrow
    ; countdownBitsNoBorrow
    ; decrementOne
    ; decrementTwo
    ; decrementFour
    ; canonicalXORCountdownBoundary
    )
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentValidation

------------------------------------------------------------------------
-- CURRENT EXACT TRUST BOUNDARY
--
-- THIS MODULE DOES NOT PROVE P != NP.
--
-- PAID ABOVE THE OCT-12 ROOT:
--
-- 1. VIRTUAL / ORDINARY STANDARD REPRESENTATION AND COSTED STREAMING
--    * virtual tape materialisation/local bisimulation is paid;
--    * own-Cook bit access is generated and costed by the same recursion;
--    * only unary index is dynamic at runtime for fixed `(machine,input,T)`;
--    * transition/acceptance local Boolean kernels are frozen finite data.
--
-- 2. ACTUAL CANDIDATE SUBMACHINE + EXACT RUN
--    * actual candidate rules embed into a linked coded target;
--    * whole candidate execution lifts edge-for-edge with identical step count;
--    * generic prefix ; candidate ; suffix exact runs compose additively.
--
-- 3. ACTUAL-HALTING RUNTIME IS INDEPENDENT OF COOK PADDING
--    * `CodedStandardCanonicalInputExact` starts the semantic machine on the
--      conventional split tape with implicit blank tails and no T parameter;
--    * `CodedStandardHaltingPolynomialDeciderExact` carries an actual quiescent
--      runtime and only a separate polynomial upper bound;
--    * actual runtime is operationally unique once quiescence/decision hold.
--
-- 4. GUARDED COOK EXECUTION IS NOW A REPRESENTATION COMPILER
--    * `StandardBlankTailBisimulationExact` identifies finite explicit blank tails
--      with the ordinary implicit blank tail and preserves `standardNext`;
--    * exact run transport preserves the literal number of steps and final state;
--    * `GuardedStandardStartBlankTailExact.guardedStandardStartBlankTailEq`
--      proves canonical input and `guardedStandardStart(input,T)` are the same
--      infinite tape representation;
--    * `CodedStandardGuardedExecutionCompilerExact` therefore constructs
--      `GuardedExecutionReceipt` from EVERY actual-halting candidate while
--      preserving its exact runtime and decision. Cook padding does not choose
--      runtime and is no longer a mathematical premise.
--
-- 5. EXACT-T QUIESCENT PHASE BOUNDARY + STATIC SIZE ACCOUNTING
--    * finite control can be lifted to `Fin (|Q|*(T+1))`;
--    * terminal phase T has no resident transition;
--    * the fixed-T candidate run lifts exactly with acceptance preserved;
--    * phase-lift size is exact: states=|Q|*(T+1), rules=T*|R|.
--
-- 6. LITERAL FIXED-DESCRIPTION BITSTREAM LOOKUP BASELINE
--    * unary cursor traversal is actual finite standard-TM syntax;
--    * a fixed finite Cook bitstream is compiled into literal stop/output rules;
--    * every in-range compiled bit is the SAME canonical queryAnswer;
--    * ordinary stop/output transition semantics are paid;
--    * no higher-order predicate is called at runtime.
--
-- 7. LITERAL SYNTACTIC SELF-FIX ROUTES ARE CLOSED
--    * full table-baked same-code self-description contradicts actual state width;
--    * strict representation growth blocks raw syntactic fixed points;
--    * the anchored literal structural compiler collapses to zero budget/clock.
--
-- 8. BEHAVIOURAL QUOTATION / INTERPRETER SEMANTICS ARE NOW PAID
--    * the actual coded finite machine has a self-delimiting quotation with
--      parser round-trip;
--    * the raw interpreter is first-order Nat/List parse/dispatch/tape recursion;
--    * `selfDelimitedInterpreterFollowsStandardRun` proves that on genuine
--      coded programs it follows every typed standard exact run edge-for-edge,
--      with the identical step count after the explicit Fin->Nat projection.
--    Therefore semantic fidelity is no longer a specializer leaf.
--
-- 9. BEHAVIOURAL KLEENE SELF-REFERENCE IS THE SURVIVING TARGET
--    `PNotEqualsNPKleeneSpecializationFixedPointExact` constructs the abstract
--    behavioural fixed point.  The old Q2 primitive erases its quoted program,
--    so it cannot instantiate the current coded candidate.
--
-- 10. XOR / RIPPLE-COUNTDOWN CROSS-POLLINATION IS NOW QUANTITATIVE
--    * binary decrement data update is `bit XOR borrowIn`;
--    * XOR is recoverable in either coordinate; borrow is a separate coordinate;
--    * a literal 3-state/3-rule timer has arbitrary-word exact runs;
--    * one decrement costs <= bitWidth+1, tight on all-zero words;
--    * the phase-vs-counter Pareto explicitly keeps static size and runtime work
--      on separate axes; neither timing architecture dominates all resources;
--    * IIT phi remains explicitly NOT complexity hardness evidence.
--
-- 11. THE FIXED RAW-INTERPRETER COMPILER IS NOW DECOMPOSED INTO LITERAL MICROCODE
--    * `CodedFiniteUnaryDelimiterScannerExact` gives a complete constant-control
--      coded TM for skipping unary-framed Nat fields;
--    * unary-field equality has one canonical dispatch authority in
--      `CodedFiniteUnaryFieldEqualityDeterminismExact`, one canonical coded
--      machine, and a thin quiescence closure;
--    * XOR is deliberately not substituted into unary equality where it would
--      require extra pairing/routing machinery.
--
-- LIVE CONSTRUCTIVE WALL AFTER THIS CUT:
--
-- A. LITERAL CODED INTERPRETER / SPECIALIZER COMPILER
--    Continue compiling the fixed parser, rule scan, field equality, tape update
--    and diagonal/specialization recursion into literal `CodedFiniteStandardTM`
--    fragments.  For unary equality, the immediate local payment is its exact
--    mark/shuttle run correctness + work bound; then assemble the finite pieces.
--
-- B. QUOTED-CODE-CONSUMING BEHAVIOURAL SELF-SPECIALIZER
--    Instantiate the already-proved Kleene construction on the ACTUAL coded
--    machine/program carrier.  The binary body must genuinely consume the
--    candidate's self-delimiting quote and produce the guarded-Cook behaviour
--    for THAT SAME code. Raw helper-code equality is not required.
--
-- C. FINAL SAME-OBJECT RESOURCE FIXED POINT
--    Construct one final target code and exact resource budget T* such that the
--    SAME code is the object described by its guarded Cook formula and the total
--    interpreter/specializer/generation/control/candidate/suffix work closes
--    under the SAME accounting. Both static description and runtime axes count.
--
-- D. TERMINAL CONTRADICTION + BARRIER AUDIT
--    Only after A-C may the existing Cook iff/opposite endpoint route produce
--    `SATDecisionFailure -> SATNotInP -> PNotEqualsNP`. Any successful closure
--    must then be audited explicitly against relativisation, algebrisation and
--    natural-proof barriers; diagonal syntax alone receives no exemption.
--
-- SOURCE STATUS: source-written/static-audited only. No Clay-level completion
-- is asserted here.
------------------------------------------------------------------------
