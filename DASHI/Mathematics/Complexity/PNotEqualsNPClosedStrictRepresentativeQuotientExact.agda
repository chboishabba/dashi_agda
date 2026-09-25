module DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact where

------------------------------------------------------------------------
-- STRUCTURALLY CLOSED STRICT REPRESENTATIVES
--
-- Existing strict-representative closure still obtains one SAT bit per quotient
-- state by querying the hypothetical polynomial decider D on a smaller
-- representative.
--
-- This owner removes even those D-calls.
--
-- A StructuralRepresentativeChain is proof data built only from:
--
--   * literal Cook formulas;
--   * strict node-count descent;
--   * equisatisfiability at each descent step;
--   * a terminal formula which is LITERALLY constant true or constant false.
--
-- No SAT oracle bit is stored in the chain.
--
-- If every quotient-state representative carries such a chain, terminal state
-- labels are computed structurally from the terminal constants.  We prove those
-- labels correct against the repository's independent constructive finite SAT
-- decider, then feed them into the exact quotient DP.
--
-- Thus the hypothetical polynomial SAT decider is no longer needed to label
-- quotient states.  The remaining theorem is the hard one: CONSTRUCT these
-- chains non-circularly from the special self-instantiation structure while
-- keeping their representation/construction inside the self-size budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.BooleanFormulaFiniteSATDecisionExact as Finite
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Literal constant satisfiability.
------------------------------------------------------------------------

constantTrueSatisfiable :
  Cook.Satisfiable (Cook.constant true)
constantTrueSatisfiable =
  Cook.satisfyingAssignment
    (λ index → false)
    refl

constantFalseUnsatisfiable :
  Cook.Satisfiable (Cook.constant false) →
  ⊥
constantFalseUnsatisfiable
    (Cook.satisfyingAssignment assignment evaluatesTrue) =
  falseNotTrue evaluatesTrue

------------------------------------------------------------------------
-- A structurally descending semantic representative chain.
------------------------------------------------------------------------

data StructuralRepresentativeChain :
    Cook.BooleanFormula →
    Set₁ where

  terminal :
    (value : Bool) →
    StructuralRepresentativeChain
      (Cook.constant value)

  descend :
    ∀ {formula smaller : Cook.BooleanFormula} →
    Strict.CookSatisfiabilityEquivalent
      formula
      smaller →
    Size.formulaNodeCount smaller
      <
    Size.formulaNodeCount formula →
    StructuralRepresentativeChain smaller →
    StructuralRepresentativeChain formula

------------------------------------------------------------------------
-- The terminal Boolean value is computed from chain syntax.
------------------------------------------------------------------------

chainTruth :
  ∀ {formula : Cook.BooleanFormula} →
  StructuralRepresentativeChain formula →
  Bool
chainTruth (terminal value) =
  value
chainTruth (descend equivalent smaller chain) =
  chainTruth chain

------------------------------------------------------------------------
-- Chain truth is exactly formula satisfiability.
------------------------------------------------------------------------

chainTruthTrueGivesSatisfiable :
  ∀ {formula : Cook.BooleanFormula}
    (chain : StructuralRepresentativeChain formula) →
  chainTruth chain ≡ true →
  Cook.Satisfiable formula
chainTruthTrueGivesSatisfiable
    (terminal true)
    truth =
  constantTrueSatisfiable
chainTruthTrueGivesSatisfiable
    (terminal false)
    ()
chainTruthTrueGivesSatisfiable
    (descend equivalent smaller chain)
    truth =
  proj₂ equivalent
    (chainTruthTrueGivesSatisfiable
      chain
      truth)

satisfiableGivesChainTruthTrue :
  ∀ {formula : Cook.BooleanFormula}
    (chain : StructuralRepresentativeChain formula) →
  Cook.Satisfiable formula →
  chainTruth chain ≡ true
satisfiableGivesChainTruthTrue
    (terminal true)
    satisfiable =
  refl
satisfiableGivesChainTruthTrue
    (terminal false)
    satisfiable =
  ⊥-elim
    (constantFalseUnsatisfiable satisfiable)
satisfiableGivesChainTruthTrue
    (descend equivalent smaller chain)
    satisfiable =
  satisfiableGivesChainTruthTrue
    chain
    (proj₁ equivalent satisfiable)

------------------------------------------------------------------------
-- Closed strict quotient: each state representative descends to a literal
-- constant without consulting D.
------------------------------------------------------------------------

record ClosedStrictRepresentativeQuotient
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor closed-strict-representative-quotient
  field
    strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient root

    representativeChain :
      (state :
        Fin
          (Quotient.stateCount
            (Strict.quotient strictQuotient))) →
      StructuralRepresentativeChain
        (Strict.representative
          strictQuotient
          state)

open ClosedStrictRepresentativeQuotient public

------------------------------------------------------------------------
-- Independent exact SAT oracle used only to VERIFY the structurally computed
-- labels.  It is not used to construct them.
------------------------------------------------------------------------

finiteSATOracle :
  SAT.SATDecisionOracle
finiteSATOracle = record
  { Search.decide =
      Finite.decideFiniteSATBool
  ; Search.sound =
      Finite.decideFiniteSATBoolSound
  ; Search.complete =
      Finite.decideFiniteSATBoolComplete
  }

------------------------------------------------------------------------
-- Structural label for one quotient state.
------------------------------------------------------------------------

closedStateTruth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      ClosedStrictRepresentativeQuotient root) →
  Fin
    (Quotient.stateCount
      (Strict.quotient
        (strictQuotient closed))) →
  Bool
closedStateTruth closed state =
  chainTruth
    (representativeChain
      closed
      state)

------------------------------------------------------------------------
-- A structurally computed state label agrees with every reachable formula in
-- that state.
------------------------------------------------------------------------

closedStateTruthCorrectForReachable :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      ClosedStrictRepresentativeQuotient root)
    {current : SAT.BooleanFormula currentVariables}
    (derivation :
      Family.RestrictionDerivation
        root
        current) →
  closedStateTruth
    closed
    (Quotient.classify
      (Strict.quotient
        (strictQuotient closed))
      derivation)
  ≡
  Finite.decideFiniteSATBool current
closedStateTruthCorrectForReachable
    closed
    {current = current}
    derivation
    with
      closedStateTruth
        closed
        state
      |
      Finite.decideFiniteSATBool current
... | true | true =
  refl
... | false | false =
  refl
... | true | false =
  falseNotTrue
    (Finite.decideFiniteSATBoolComplete
      current
      currentSat)
  where
    strict :
      Strict.StrictSemanticRepresentativeQuotient root
    strict =
      strictQuotient closed

    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient strict

    state :
      Fin (Quotient.stateCount quotient)
    state =
      Quotient.classify quotient derivation

    representativeSat :
      Cook.Satisfiable
        (Strict.representative strict state)
    representativeSat =
      chainTruthTrueGivesSatisfiable
        (representativeChain closed state)
        refl

    equivalent :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (Strict.representative strict state)
    equivalent =
      Strict.representativeEquivalent
        strict
        derivation

    currentCookSat :
      Cook.Satisfiable
        (Bridge.indexedToCook current)
    currentCookSat =
      proj₂ equivalent representativeSat

    currentSat :
      SAT.Satisfying current
    currentSat =
      Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
        current
        currentCookSat
... | false | true =
  falseNotTrue
    (sym
      chainMustBeTrue)
  where
    strict :
      Strict.StrictSemanticRepresentativeQuotient root
    strict =
      strictQuotient closed

    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient strict

    state :
      Fin (Quotient.stateCount quotient)
    state =
      Quotient.classify quotient derivation

    currentSat :
      SAT.Satisfying current
    currentSat =
      Finite.decideFiniteSATBoolSound
        current
        refl

    currentCookSat :
      Cook.Satisfiable
        (Bridge.indexedToCook current)
    currentCookSat =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        current
        currentSat

    equivalent :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (Strict.representative strict state)
    equivalent =
      Strict.representativeEquivalent
        strict
        derivation

    representativeSat :
      Cook.Satisfiable
        (Strict.representative strict state)
    representativeSat =
      proj₁ equivalent currentCookSat

    chainMustBeTrue :
      chainTruth
        (representativeChain closed state)
      ≡ true
    chainMustBeTrue =
      satisfiableGivesChainTruthTrue
        (representativeChain closed state)
        representativeSat

------------------------------------------------------------------------
-- Structural terminal-state labelling for the exact quotient DP.
------------------------------------------------------------------------

closedTerminalLabels :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      ClosedStrictRepresentativeQuotient root) →
  DP.TerminalStateLabelling
    (Strict.quotient
      (strictQuotient closed))
    finiteSATOracle
closedTerminalLabels closed =
  DP.terminal-state-labelling
    (closedStateTruth closed)
    terminalCorrect
  where
    terminalCorrect :
      ∀ {terminal : SAT.BooleanFormula 0}
        (derivation :
          Family.RestrictionDerivation
            root
            terminal) →
      closedStateTruth
        closed
        (Quotient.classify
          (Strict.quotient
            (strictQuotient closed))
          derivation)
      ≡
      Finite.decideFiniteSATBool terminal
    terminalCorrect =
      closedStateTruthCorrectForReachable
        closed

------------------------------------------------------------------------
-- Root SAT decision follows from structural chains + quotient DP, with no D
-- query in the state labels.
------------------------------------------------------------------------

closedRepresentativeDPComputesRoot :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (closed :
      ClosedStrictRepresentativeQuotient root) →
  DP.quotientTruthAtDepth
    (Strict.quotient
      (strictQuotient closed))
    (closedTerminalLabels closed)
    rootVariables
    (Quotient.classify
      (Strict.quotient
        (strictQuotient closed))
      Family.restrictionRoot)
  ≡
  Finite.decideFiniteSATBool root
closedRepresentativeDPComputesRoot closed =
  DP.quotientTruthComputesRootDecision
    (Strict.quotient
      (strictQuotient closed))
    finiteSATOracle
    (closedTerminalLabels closed)

------------------------------------------------------------------------
-- Research consequence.
--
-- There is now a fully non-D-labelled quotient closure theorem:
--
--   structural strict chains to literal constants
--      -> exact state truth
--      -> exact finite quotient DP
--      -> exact root SAT truth.
--
-- No hypothetical polynomial SAT decision is used to populate the state table.
--
-- This sharpens the live mathematical target again.  A Clay-relevant
-- self-diagonal construction must produce, from finite code(D) and the special
-- self-instantiation structure:
--
--   * the root-scoped quotient/order;
--   * strict representatives;
--   * structural descending chains to literal constants;
--   * all within a resource budget that closes the bounded fixed point.
--
-- Merely proving these objects EXIST is still not enough if their constructor
-- hides SAT.  Their construction/provenance remains the open theorem.
------------------------------------------------------------------------
