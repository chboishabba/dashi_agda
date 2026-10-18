module DASHI.Mathematics.Complexity.PNotEqualsNPQ2TerminatingQuoteCollapseExact where

------------------------------------------------------------------------
-- TERMINATING-QUOTE COLLAPSE FOR THE CONCRETE Q2 FINITE-CODE EXECUTOR
--
-- The current Q2 primitive binary semantics ignores its quoted-program argument
-- and returns one canonical terminal formula.  The finite code grammar adds
-- specialization/diagonalization syntax around that primitive, but it does not
-- create new terminating outputs.
--
-- Hence:
--
--   every terminating quoted program
--       returns
--   canonicalTerminalFormula.
--
-- This matters for the residual-width programme.  The "all quoted programs"
-- premise in Q1OppositeSATTerminalSemantics is NOT a hidden universality source
-- for the concrete executor.  It is equivalent to one opposite-SAT condition
-- on the canonical terminal formula itself.
--
-- Therefore any special small-width law still needed by Q1 must come from the
-- construction/resource/descent laws that manufacture that terminal formula,
-- not from quantification over quoted programs in this executor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact as Exec
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact as ClayClosure

------------------------------------------------------------------------
-- Maybe.just is injective.
------------------------------------------------------------------------

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

------------------------------------------------------------------------
-- Binary execution can terminate only with the one canonical terminal formula.
------------------------------------------------------------------------

q2Run2TerminatingOutputIsCanonical :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  (program quoted : Code.Program Exec.Q2Primitive) →
  (output : Cook.BooleanFormula) →
  Code.run2
      (Exec.q2PrimitiveSemantics stepSystem initial)
      program
      quoted
      tt
  ≡
  just output →
  output
  ≡
  Exec.canonicalTerminalFormula stepSystem initial
q2Run2TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.primitive Exec.runBoundedDescent)
    quoted
    output
    equality =
  sym (justInjective equality)
q2Run2TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.specialized program static)
    quoted
    output
    ()
q2Run2TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.diagonalized program)
    quoted
    output
    equality =
  q2Run2TerminatingOutputIsCanonical
    stepSystem
    initial
    program
    (Code.specialized quoted quoted)
    output
    equality

------------------------------------------------------------------------
-- Unary quoted-program execution has the same collapse.
------------------------------------------------------------------------

q2Run1TerminatingOutputIsCanonical :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  (quoted : Code.Program Exec.Q2Primitive) →
  (output : Cook.BooleanFormula) →
  Code.run1
      (Exec.q2PrimitiveSemantics stepSystem initial)
      quoted
      tt
  ≡
  just output →
  output
  ≡
  Exec.canonicalTerminalFormula stepSystem initial
q2Run1TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.primitive Exec.runBoundedDescent)
    output
    ()
q2Run1TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.specialized program static)
    output
    equality =
  q2Run2TerminatingOutputIsCanonical
    stepSystem
    initial
    program
    static
    output
    equality
q2Run1TerminatingOutputIsCanonical
    stepSystem
    initial
    (Code.diagonalized program)
    output
    ()

------------------------------------------------------------------------
-- Same theorem stated on the PartialKleene interface used by the Clay closure.
------------------------------------------------------------------------

q2AnyTerminatingQuotedOutputIsCanonical :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  (quoted : Code.Program Exec.Q2Primitive) →
  (output : Cook.BooleanFormula) →
  Kleene.run1
      (Exec.q2PartialSystem stepSystem initial)
      quoted
      tt
  ≡
  just output →
  output
  ≡
  Exec.canonicalTerminalFormula stepSystem initial
q2AnyTerminatingQuotedOutputIsCanonical =
  q2Run1TerminatingOutputIsCanonical

------------------------------------------------------------------------
-- The single terminal opposite-SAT condition.
------------------------------------------------------------------------

TerminalOppositeSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.PolynomialSATDeciderCandidate cost →
  Q2.BoundedSelfReferenceStepSystem →
  Q2.BoundedSelfReferenceState →
  Set
TerminalOppositeSAT
    candidate
    stepSystem
    initial =
  let terminalFormula =
        Exec.canonicalTerminalFormula
          stepSystem
          initial
  in
  (Direct.decide candidate terminalFormula ≡ false →
    Cook.Satisfiable terminalFormula)
  ×
  (Cook.Satisfiable terminalFormula →
    Direct.decide candidate terminalFormula ≡ false)

------------------------------------------------------------------------
-- All-quotes Q1 semantics immediately gives the terminal condition by choosing
-- the concrete terminating fixed-point quote.
------------------------------------------------------------------------

q1AllQuotesGivesTerminalOppositeSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  ClayClosure.Q1OppositeSATTerminalSemantics
    candidate
    stepSystem
    initial →
  TerminalOppositeSAT
    candidate
    stepSystem
    initial
q1AllQuotesGivesTerminalOppositeSAT
    candidate
    stepSystem
    initial
    q1Semantics =
  q1Semantics
    (Exec.q2FixedPointProgram stepSystem initial)
    (Exec.canonicalTerminalFormula stepSystem initial)
    (Exec.q2FixedPointRunsToCanonicalTerminalFormula
      stepSystem
      initial)

------------------------------------------------------------------------
-- Conversely, because every terminating quote has that same output, the one
-- terminal condition reconstructs the full all-quotes premise.
------------------------------------------------------------------------

terminalOppositeSATGivesQ1AllQuotes :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  TerminalOppositeSAT
    candidate
    stepSystem
    initial →
  ClayClosure.Q1OppositeSATTerminalSemantics
    candidate
    stepSystem
    initial
terminalOppositeSATGivesQ1AllQuotes
    candidate
    stepSystem
    initial
    terminalSemantics
    quoted
    quotedOutput
    quotedTerminates =
  satisfiableIfRejected
  ,
  rejectedIfSatisfiable
  where
    terminalFormula :
      Cook.BooleanFormula
    terminalFormula =
      Exec.canonicalTerminalFormula
        stepSystem
        initial

    outputExact :
      quotedOutput ≡ terminalFormula
    outputExact =
      q2AnyTerminatingQuotedOutputIsCanonical
        stepSystem
        initial
        quoted
        quotedOutput
        quotedTerminates

    decisionTransport :
      Direct.decide candidate quotedOutput
      ≡
      Direct.decide candidate terminalFormula
    decisionTransport =
      cong
        (Direct.decide candidate)
        outputExact

    satisfiableIfRejected :
      Direct.decide candidate quotedOutput ≡ false →
      Cook.Satisfiable terminalFormula
    satisfiableIfRejected rejected =
      let
        terminalRejected :
          Direct.decide candidate terminalFormula ≡ false
        terminalRejected =
          trans
            (sym decisionTransport)
            rejected
      in
      proj₁ terminalSemantics
        terminalRejected

    rejectedIfSatisfiable :
      Cook.Satisfiable terminalFormula →
      Direct.decide candidate quotedOutput ≡ false
    rejectedIfSatisfiable satisfiable =
      trans
        decisionTransport
        (proj₂ terminalSemantics
          satisfiable)

------------------------------------------------------------------------
-- Exact equivalence of the apparently-global and actually-local obligations.
------------------------------------------------------------------------

q1AllQuotesIffTerminalOppositeSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  (ClayClosure.Q1OppositeSATTerminalSemantics
      candidate
      stepSystem
      initial →
    TerminalOppositeSAT
      candidate
      stepSystem
      initial)
  ×
  (TerminalOppositeSAT
      candidate
      stepSystem
      initial →
    ClayClosure.Q1OppositeSATTerminalSemantics
      candidate
      stepSystem
      initial)
q1AllQuotesIffTerminalOppositeSAT
    candidate
    stepSystem
    initial =
  q1AllQuotesGivesTerminalOppositeSAT
    candidate
    stepSystem
    initial
  ,
  terminalOppositeSATGivesQ1AllQuotes
    candidate
    stepSystem
    initial

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The current finite-code executor has no cross-quote payload family to exploit:
--
--   terminating quote outputs = one canonical terminal formula.
--
-- Therefore the remaining semantic-width question is entirely:
--
--   what residual width can the Q1/Q2 construction produce for THAT terminal
--   formula while also satisfying the charged strict-descent/resource laws?
--
-- Quantification over quoted programs does not itself supply a small-width
-- invariant and does not block a high-width terminal formula.
------------------------------------------------------------------------
