module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact where

------------------------------------------------------------------------
-- LAYERED RESIDUAL-FUNCTION WIDTH OF A SHANNON RESTRICTION FAMILY
--
-- The future-congruence owner proves, at fixed remaining arity:
--
--   FutureEquivalent
--     iff
--   equality of the residual Boolean functions.
--
-- This file turns that semantic normalization into a literal finite-state
-- lower bound for every honest Q1 quotient.
--
-- A width witness of size w at remaining arity r is an enumeration of w
-- reachable restriction nodes whose residual Boolean functions are pairwise
-- distinct.
--
-- Main theorem:
--
--   width witness w at layer r
--       ->
--   w <= stateCount(Q)
--
-- for every Q1 quotient Q on the same root.
--
-- CROSS-LAYER BOUNDARY:
--
-- The legacy Q1 quotient interface permits cross-layer state reuse, so only
-- per-layer lower bounds are unconditional there.  The newer preferred finite
-- candidate path carries explicit state arity and therefore forbids such reuse;
-- on that path the literal sum of the per-layer widths is a valid lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as FinBase
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_ ; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Core.FutureObservationalRefinement as FutureCore
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational

------------------------------------------------------------------------
-- A reachable node known to live at one exact remaining arity.
------------------------------------------------------------------------

record LayerNode
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining : Nat) : Set₁ where
  constructor layer-node
  field
    node :
      Family.RestrictionNode root

    arityExact :
      Family.currentVariables node
      ≡ remaining

open LayerNode public

------------------------------------------------------------------------
-- Residual-function equality inside one layer.
------------------------------------------------------------------------

LayerResidualEqual :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  LayerNode {root = root} remaining →
  LayerNode {root = root} remaining →
  Set
LayerResidualEqual left right =
  (assignment : SAT.Assignment remaining) →
  SAT.evaluate
      (Family.currentFormula (node left))
      (Future.transportAssignment
        (sym (arityExact left))
        assignment)
  ≡
  SAT.evaluate
      (Family.currentFormula (node right))
      (Future.transportAssignment
        (sym (arityExact right))
        assignment)

------------------------------------------------------------------------
-- A finite family of pairwise semantically distinct residuals.
--
-- Extensional formulation:
-- if two enumerated residual functions are equal, the indices were equal.
------------------------------------------------------------------------

record ResidualWidthWitness
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining width : Nat) : Set₁ where
  constructor residual-width-witness
  field
    representative :
      Fin width →
      LayerNode {root = root} remaining

    residualEqualIndicesEqual :
      ∀ {left right : Fin width} →
      LayerResidualEqual
        (representative left)
        (representative right) →
      left ≡ right

open ResidualWidthWitness public

------------------------------------------------------------------------
-- Q1 classification of a width witness.
------------------------------------------------------------------------

widthWitnessClassify :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (witness : ResidualWidthWitness remaining width) →
  Fin width →
  Fin (Quotient.stateCount quotient)
widthWitnessClassify quotient witness index =
  Quotient.classify
    quotient
    (Family.derivation
      (node
        (representative witness index)))

------------------------------------------------------------------------
-- Same Q1 state forces residual equality, hence width-witness indices equal.
------------------------------------------------------------------------

widthWitnessClassifyInjective :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (witness : ResidualWidthWitness remaining width)
    {left right : Fin width} →
  widthWitnessClassify quotient witness left
  ≡
  widthWitnessClassify quotient witness right →
  left ≡ right
widthWitnessClassifyInjective
    quotient
    witness
    {left}
    {right}
    sameState =
  residualEqualIndicesEqual witness
    residualEqual
  where
    leftNode :
      LayerNode remaining
    leftNode =
      representative witness left

    rightNode :
      LayerNode remaining
    rightNode =
      representative witness right

    sameArity :
      Family.currentVariables (node leftNode)
      ≡
      Family.currentVariables (node rightNode)
    sameArity =
      trans
        (arityExact leftNode)
        (sym (arityExact rightNode))

    pointwise :
      (assignment :
        SAT.Assignment
          (Family.currentVariables (node leftNode))) →
      SAT.evaluate
          (Family.currentFormula (node leftNode))
          assignment
      ≡
      SAT.evaluate
          (Family.currentFormula (node rightNode))
          (Future.transportAssignment
            sameArity
            assignment)
    pointwise =
      Future.sameLayerSameQ1StateImpliesPointwiseResidualEquality
        quotient
        sameArity
        sameState

    residualEqual :
      LayerResidualEqual leftNode rightNode
    residualEqual assignment
        with arityExact leftNode
           | arityExact rightNode
    ... | refl | refl =
      pointwise assignment

------------------------------------------------------------------------
-- Main per-layer semantic width lower bound.
------------------------------------------------------------------------

residualWidthBelowQ1StateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  ResidualWidthWitness remaining width →
  width ≤ Quotient.stateCount quotient
residualWidthBelowQ1StateCount quotient witness =
  FinP.injective⇒≤
    (widthWitnessClassifyInjective quotient witness)

------------------------------------------------------------------------
-- Exact-width certificate.
--
-- This avoids choosing a quotient implementation: width is exact when
--
--  1. width distinct residual functions are exhibited; and
--  2. every other finite same-layer future-distinct family has size <= width.
------------------------------------------------------------------------

record ExactResidualWidth
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (remaining width : Nat) : Set₁ where
  constructor exact-residual-width
  field
    lowerWitness :
      ResidualWidthWitness {root = root} remaining width

    maximal :
      ∀ {candidateWidth : Nat} →
      ResidualWidthWitness {root = root} remaining candidateWidth →
      candidateWidth ≤ width

open ExactResidualWidth public

exactResidualWidthBelowQ1StateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  ExactResidualWidth {root = root} remaining width →
  width ≤ Quotient.stateCount quotient
exactResidualWidthBelowQ1StateCount quotient exact =
  residualWidthBelowQ1StateCount
    quotient
    (lowerWitness exact)

------------------------------------------------------------------------
-- Width profile.
--
-- We index by remaining arity rather than restriction depth.  For a root with
-- n variables, remaining arity r corresponds to depth n-r.
------------------------------------------------------------------------

record ResidualWidthProfile
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor residual-width-profile
  field
    widthAt :
      (remaining : Nat) →
      remaining ≤ rootVariables →
      Nat

    exactAt :
      (remaining : Nat) →
      (inRoot : remaining ≤ rootVariables) →
      ExactResidualWidth
        {root = root}
        remaining
        (widthAt remaining inRoot)

open ResidualWidthProfile public

profileLayerBelowQ1StateCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (profile : ResidualWidthProfile root)
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (remaining : Nat)
    (inRoot : remaining ≤ rootVariables) →
  widthAt profile remaining inRoot
  ≤
  Quotient.stateCount quotient
profileLayerBelowQ1StateCount
    profile quotient remaining inRoot =
  exactResidualWidthBelowQ1StateCount
    quotient
    (exactAt profile remaining inRoot)

------------------------------------------------------------------------
-- Preferred finite-candidate path: arity tracking forbids cross-layer reuse.
------------------------------------------------------------------------

candidateWidthClassify :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (witness : ResidualWidthWitness {root = root} remaining width) →
  Fin width →
  Fin (Candidate.stateCount candidate)
candidateWidthClassify candidate witness index =
  Candidate.candidateSelect
    candidate
    (Family.derivation
      (node
        (representative witness index)))

candidateWidthClassifyInjective :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTerminal.ArityTrackedTerminalAdmission candidate)
    (witness : ResidualWidthWitness {root = root} remaining width)
    {left right : Fin width} →
  candidateWidthClassify candidate witness left
  ≡
  candidateWidthClassify candidate witness right →
  left ≡ right
candidateWidthClassifyInjective
    admission
    witness
    {left}
    {right}
    sameState =
  residualEqualIndicesEqual witness residualEqual
  where
    leftNode :
      LayerNode remaining
    leftNode =
      representative witness left

    rightNode :
      LayerNode remaining
    rightNode =
      representative witness right

    futureEquivalent :
      FutureCore.FutureEquivalent
        (Future.restrictionActionSystem _)
        Future.restrictionObservation
        (node leftNode)
        (node rightNode)
    futureEquivalent =
      ArityTerminal.sameGeneratedStateContainedInFutureEquivalent
        admission
        sameState

    sameArity :
      Family.currentVariables (node leftNode)
      ≡
      Family.currentVariables (node rightNode)
    sameArity =
      trans
        (arityExact leftNode)
        (sym (arityExact rightNode))

    pointwise :
      (assignment :
        SAT.Assignment
          (Family.currentVariables (node leftNode))) →
      SAT.evaluate
          (Family.currentFormula (node leftNode))
          assignment
      ≡
      SAT.evaluate
          (Family.currentFormula (node rightNode))
          (Future.transportAssignment sameArity assignment)
    pointwise =
      Future.futureEquivalentImpliesPointwiseEvaluationEqual
        sameArity
        futureEquivalent

    residualEqual :
      LayerResidualEqual leftNode rightNode
    residualEqual assignment
        with arityExact leftNode
           | arityExact rightNode
    ... | refl | refl =
      pointwise assignment

residualWidthBelowArityAdmittedCandidateStateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  ResidualWidthWitness {root = root} remaining width →
  width ≤ Candidate.stateCount candidate
residualWidthBelowArityAdmittedCandidateStateCount admission witness =
  FinP.injective⇒≤
    (candidateWidthClassifyInjective admission witness)

------------------------------------------------------------------------
-- Recursive all-layer width stack.
--
-- ResidualWidthStack next total contains one width witness for every layer
--
--   next-1, next-2, ..., 0
--
-- and its type-level total is the literal sum of those widths.
------------------------------------------------------------------------

data ResidualWidthStack
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} :
    Nat →
    Nat →
    Set₁ where

  widthStackEmpty :
    ResidualWidthStack {root = root} 0 0

  widthStackPush :
    ∀ {remaining width tailTotal : Nat} →
    ResidualWidthWitness {root = root} remaining width →
    ResidualWidthStack {root = root} remaining tailTotal →
    ResidualWidthStack
      {root = root}
      (suc remaining)
      (width + tailTotal)

------------------------------------------------------------------------
-- Enumerate every semantic class represented by a width stack.
------------------------------------------------------------------------

stackNode :
  ∀ {rootVariables next total : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  ResidualWidthStack {root = root} next total →
  Fin total →
  Family.RestrictionNode root
stackNode widthStackEmpty ()
stackNode
    (widthStackPush {width = width} {tailTotal = tailTotal}
      headWitness tailStack)
    index
    with FinBase.splitAt width index
... | inj₁ headIndex =
  node (representative headWitness headIndex)
... | inj₂ tailIndex =
  stackNode tailStack tailIndex

stackNodeArityBelowNext :
  ∀ {rootVariables next total : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (stack : ResidualWidthStack {root = root} next total)
    (index : Fin total) →
  Family.currentVariables (stackNode stack index)
  < next
stackNodeArityBelowNext widthStackEmpty ()
stackNodeArityBelowNext
    (widthStackPush
      {remaining = remaining}
      {width = width}
      headWitness
      tailStack)
    index
    with FinBase.splitAt width index
... | inj₁ headIndex =
  substRight
    (arityExact
      (representative headWitness headIndex))
    (NatP.n<1+n remaining)
  where
    substRight :
      ∀ {left right bound : Nat} →
      left ≡ right →
      right < bound →
      left < bound
    substRight refl proof = proof
... | inj₂ tailIndex =
  NatP.<-trans
    (stackNodeArityBelowNext tailStack tailIndex)
    (NatP.n<1+n remaining)

stackCandidateClassify :
  ∀ {rootVariables next total : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (candidate : Candidate.TransitionTableCandidate root) →
  ResidualWidthStack {root = root} next total →
  Fin total →
  Fin (Candidate.stateCount candidate)
stackCandidateClassify candidate stack index =
  Candidate.candidateSelect
    candidate
    (Family.derivation
      (stackNode stack index))

------------------------------------------------------------------------
-- The stack classifier is injective for any arity-tracked admission.
------------------------------------------------------------------------

stackCandidateClassifyInjective :
  ∀ {rootVariables next total : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTerminal.ArityTrackedTerminalAdmission candidate)
    (stack : ResidualWidthStack {root = root} next total)
    {left right : Fin total} →
  stackCandidateClassify candidate stack left
  ≡
  stackCandidateClassify candidate stack right →
  left ≡ right
stackCandidateClassifyInjective
    admission
    widthStackEmpty
    {left = ()}
stackCandidateClassifyInjective
    {candidate = candidate}
    admission
    (widthStackPush
      {remaining = remaining}
      {width = width}
      {tailTotal = tailTotal}
      headWitness
      tailStack)
    {left}
    {right}
    sameState
    with FinBase.splitAt width left
       | FinBase.splitAt width right
       | FinP.join-splitAt width tailTotal left
       | FinP.join-splitAt width tailTotal right
... | inj₁ leftHead | inj₁ rightHead | leftJoin | rightJoin =
  trans
    (sym leftJoin)
    (trans
      (congJoinHead
        (candidateWidthClassifyInjective
          admission
          headWitness
          sameState))
      rightJoin)
  where
    congJoinHead :
      leftHead ≡ rightHead →
      FinBase.join width tailTotal (inj₁ leftHead)
      ≡
      FinBase.join width tailTotal (inj₁ rightHead)
    congJoinHead refl = refl

... | inj₂ leftTail | inj₂ rightTail | leftJoin | rightJoin =
  trans
    (sym leftJoin)
    (trans
      (congJoinTail
        (stackCandidateClassifyInjective
          admission
          tailStack
          sameState))
      rightJoin)
  where
    congJoinTail :
      leftTail ≡ rightTail →
      FinBase.join width tailTotal (inj₂ leftTail)
      ≡
      FinBase.join width tailTotal (inj₂ rightTail)
    congJoinTail refl = refl

... | inj₁ leftHead | inj₂ rightTail | leftJoin | rightJoin =
  ⊥-elim
    (NatP.<⇒≱
      (stackNodeArityBelowNext tailStack rightTail)
      sameArityReverse)
  where
    sameArity :
      Family.currentVariables
        (node (representative headWitness leftHead))
      ≡
      Family.currentVariables
        (stackNode tailStack rightTail)
    sameArity =
      ArityTerminal.sameSelectedStateImpliesSameArity
        admission
        (Family.derivation
          (node (representative headWitness leftHead)))
        (Family.derivation
          (stackNode tailStack rightTail))
        sameState

    sameArityReverse :
      remaining
      ≤
      Family.currentVariables
        (stackNode tailStack rightTail)
    sameArityReverse
      rewrite arityExact
        (representative headWitness leftHead)
            | sameArity =
      NatP.≤-refl

... | inj₂ leftTail | inj₁ rightHead | leftJoin | rightJoin =
  ⊥-elim
    (NatP.<⇒≱
      (stackNodeArityBelowNext tailStack leftTail)
      sameArityReverse)
  where
    sameArity :
      Family.currentVariables
        (stackNode tailStack leftTail)
      ≡
      Family.currentVariables
        (node (representative headWitness rightHead))
    sameArity =
      ArityTerminal.sameSelectedStateImpliesSameArity
        admission
        (Family.derivation
          (stackNode tailStack leftTail))
        (Family.derivation
          (node (representative headWitness rightHead)))
        sameState

    sameArityReverse :
      remaining
      ≤
      Family.currentVariables
        (stackNode tailStack leftTail)
    sameArityReverse
      rewrite sameArity
            | arityExact
                (representative headWitness rightHead) =
      NatP.≤-refl

------------------------------------------------------------------------
-- Literal summed-layer lower bound.
------------------------------------------------------------------------

layeredResidualWidthSumBelowCandidateStateCount :
  ∀ {rootVariables next total : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  ResidualWidthStack {root = root} next total →
  total ≤ Candidate.stateCount candidate
layeredResidualWidthSumBelowCandidateStateCount admission stack =
  FinP.injective⇒≤
    (stackCandidateClassifyInjective admission stack)

------------------------------------------------------------------------
-- Weld summed semantic width to the actual charged operational Q1 run.
------------------------------------------------------------------------

arityTerminalOperationalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ArityTerminal.ArityTerminalAdmittedConstructionRun state →
  Operational.OperationalQ1ConstructionRun state
arityTerminalOperationalRun run =
  Candidate.admittedFiniteRunToOperationalRun
    (ArityTerminal.arityTerminalRunToAdmittedFiniteRun run)

arityTerminalRunStateCountExact :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ArityTerminal.ArityTerminalAdmittedConstructionRun state) →
  Candidate.stateCount
      (Candidate.transitionCandidate
        (Candidate.finiteCandidate
          (ArityTerminal.construction run)))
  ≡
  Operational.q1WitnessStateCount
    (Operational.q1Witness
      (arityTerminalOperationalRun run))
arityTerminalRunStateCountExact run =
  refl

layeredResidualWidthSumStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : ArityTerminal.ArityTerminalAdmittedConstructionRun state) →
  ResidualWidthStack
    {root =
      DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  total
  <
  Q2.recursiveMeasure state
layeredResidualWidthSumStrictlyBelowCurrentMeasure
    {state}
    run
    stack =
  NatP.≤-<-trans
    widthBelowCandidate
    candidateBelowMeasure
  where
    candidate :
      Candidate.TransitionTableCandidate
        (DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact.cookToIndexed
          (Q2.currentFormula state))
    candidate =
      Candidate.transitionCandidate
        (Candidate.finiteCandidate
          (ArityTerminal.construction run))

    widthBelowCandidate :
      total ≤ Candidate.stateCount candidate
    widthBelowCandidate =
      layeredResidualWidthSumBelowCandidateStateCount
        (ArityTerminal.localAdmission run)
        stack

    candidateBelowMeasure :
      Candidate.stateCount candidate
      <
      Q2.recursiveMeasure state
    candidateBelowMeasure
      rewrite arityTerminalRunStateCountExact run =
      Operational.stateCountStrictlyBelowCurrentMeasure
        (arityTerminalOperationalRun run)

------------------------------------------------------------------------
-- Three graph cells per semantic state: one node plus two Boolean transitions.
------------------------------------------------------------------------

triple : Nat → Nat
triple n =
  n + (n + n)

tripleMonotone :
  ∀ {left right : Nat} →
  left ≤ right →
  triple left ≤ triple right
tripleMonotone leftBelowRight =
  NatP.+-mono-≤
    leftBelowRight
    (NatP.+-mono-≤
      leftBelowRight
      leftBelowRight)

twoTimes :
  (n : Nat) →
  (suc (suc zero)) * n
  ≡
  n + n
twoTimes n =
  refl

operationalGraphCellCountIsTriple :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : Operational.OperationalQ1ConstructionRun state) →
  Operational.q1WitnessGraphCellCount
      (Operational.q1Witness run)
  ≡
  triple
    (Operational.q1WitnessStateCount
      (Operational.q1Witness run))
operationalGraphCellCountIsTriple run
    rewrite
      Operational.q1WitnessGraphCellCountExact
        (Operational.q1Witness run)
      |
      twoTimes
        (Operational.q1WitnessStateCount
          (Operational.q1Witness run)) =
  refl

tripleLayeredResidualWidthStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : ArityTerminal.ArityTerminalAdmittedConstructionRun state) →
  ResidualWidthStack
    {root =
      DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  triple total
  <
  Q2.recursiveMeasure state
tripleLayeredResidualWidthStrictlyBelowCurrentMeasure
    {state}
    run
    stack =
  NatP.≤-<-trans
    tripleWidthBelowGraph
    (Operational.graphCellCountStrictlyBelowCurrentMeasure
      operationalRun)
  where
    operationalRun :
      Operational.OperationalQ1ConstructionRun state
    operationalRun =
      arityTerminalOperationalRun run

    candidate :
      Candidate.TransitionTableCandidate
        (DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact.cookToIndexed
          (Q2.currentFormula state))
    candidate =
      Candidate.transitionCandidate
        (Candidate.finiteCandidate
          (ArityTerminal.construction run))

    widthBelowCandidate :
      total ≤ Candidate.stateCount candidate
    widthBelowCandidate =
      layeredResidualWidthSumBelowCandidateStateCount
        (ArityTerminal.localAdmission run)
        stack

    widthBelowOperationalStateCount :
      total
      ≤
      Operational.q1WitnessStateCount
        (Operational.q1Witness operationalRun)
    widthBelowOperationalStateCount
      rewrite
        sym (arityTerminalRunStateCountExact run) =
      widthBelowCandidate

    tripleWidthBelowOperationalTriple :
      triple total
      ≤
      triple
        (Operational.q1WitnessStateCount
          (Operational.q1Witness operationalRun))
    tripleWidthBelowOperationalTriple =
      tripleMonotone widthBelowOperationalStateCount

    tripleWidthBelowGraph :
      triple total
      ≤
      Operational.q1WitnessGraphCellCount
        (Operational.q1Witness operationalRun)
    tripleWidthBelowGraph
      rewrite operationalGraphCellCountIsTriple operationalRun =
      tripleWidthBelowOperationalTriple

------------------------------------------------------------------------
-- Cross-layer reuse boundary.
------------------------------------------------------------------------

record AritySeparatedQ1
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) : Set₁ where
  constructor arity-separated-q1
  field
    sameStateImpliesSameArity :
      {left right : Family.RestrictionNode root} →
      Quotient.classify quotient
          (Family.derivation left)
      ≡
      Quotient.classify quotient
          (Family.derivation right) →
      Family.currentVariables left
      ≡
      Family.currentVariables right

open AritySeparatedQ1 public

------------------------------------------------------------------------
-- Typed warning: the existing Q1 specification does not itself inhabit
-- AritySeparatedQ1.  Any summed-layer width theorem must consume this extra
-- separation theorem or an equivalent valid cross-layer normalization.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The semantic lower bound is now quotient-independent:
--
--   W_r(root) <= stateCount(Q)
--
-- at every Shannon layer r.
--
-- Summing W_r across layers is proved above for the preferred arity-admitted
-- candidate path.  It is not automatic for the older legacy quotient surface.
--
-- The next falsification test is therefore about the SPECIAL self-instantiated
-- roots: can generic high-width residual families be embedded into those roots
-- while preserving a layer's residual-function distinctions?
------------------------------------------------------------------------
