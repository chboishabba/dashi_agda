module DASHI.Mathematics.Complexity.PNotEqualsNPQ1RestrictionTraceRepairGeneratorExact where

------------------------------------------------------------------------
-- RESTRICTION-TRACE REPAIR GENERATOR
--
-- The coarse/fine repair boundary permits the repair coordinate to retain
-- semantic distinctions without requiring one independent construction query
-- per final Q1 state.
--
-- This owner gives the strongest cheap positive baseline available from the
-- literal Shannon family itself.
--
-- For a reachable restriction node, retain only the reverse restriction trace:
--
--   newest action :: ... :: oldest action.
--
-- One Shannon child then updates the repair by ONE list constructor:
--
--   R_(a rho) = a :: R_rho.
--
-- Because restriction from a fixed root is deterministic, equal traces at one
-- fixed remaining arity determine equal residual formulas and hence equal
-- residual Boolean functions.
--
-- Therefore cheap local repair GENERATION is genuinely possible.  This does
-- not reduce the number of distinct semantic Q1 states: distinct prefixes may
-- still require distinct trace repairs, and the existing state-count/evaluator
-- lower bounds remain untouched.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1GradedShannonRepairGeneratorExact as Shannon

------------------------------------------------------------------------
-- Reverse Shannon history.
------------------------------------------------------------------------

reverseRestrictionTrace :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  List Bool
reverseRestrictionTrace Family.restrictionRoot =
  []
reverseRestrictionTrace
    (Family.restrictionFalse derivation) =
  false ∷ reverseRestrictionTrace derivation
reverseRestrictionTrace
    (Family.restrictionTrue derivation) =
  true ∷ reverseRestrictionTrace derivation

traceRepair :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  List Bool
traceRepair layer =
  reverseRestrictionTrace
    (Family.derivation (Width.node layer))

------------------------------------------------------------------------
-- Exact one-constructor repair update.
------------------------------------------------------------------------

traceRepairStepExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (parent :
      Width.LayerNode {root = root} (suc remaining)) →
  traceRepair (Shannon.layerChild action parent)
  ≡
  action ∷ traceRepair parent
traceRepairStepExact
    {remaining = remaining}
    false
    parent
    with Width.node parent | Width.arityExact parent
... | Family.restriction-node .(suc remaining) current derivation | refl =
  refl
traceRepairStepExact
    {remaining = remaining}
    true
    parent
    with Width.node parent | Width.arityExact parent
... | Family.restriction-node .(suc remaining) current derivation | refl =
  refl

restrictionTraceRepairGenerator :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Shannon.GradedQ1RepairGenerator root
restrictionTraceRepairGenerator root =
  record
    { Shannon.Coarse =
        λ remaining → ⊤
    ; Shannon.Repair =
        λ remaining → List Bool
    ; Shannon.coarse =
        λ remaining node → tt
    ; Shannon.repair =
        λ remaining node → traceRepair node
    ; Shannon.repairStep =
        λ remaining action coarse parentRepair →
          action ∷ parentRepair
    ; Shannon.repairStepExact =
        λ remaining action parent →
          traceRepairStepExact action parent
    }

------------------------------------------------------------------------
-- Trace determinism.
--
-- At equal remaining arity, the reverse action trace determines the actual
-- residual formula because restrictHead is deterministic.
------------------------------------------------------------------------

sameReverseTraceDerivationsSameFormula :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {left right : SAT.BooleanFormula currentVariables} →
  (leftDerivation :
    Family.RestrictionDerivation root left) →
  (rightDerivation :
    Family.RestrictionDerivation root right) →
  reverseRestrictionTrace leftDerivation
    ≡
  reverseRestrictionTrace rightDerivation →
  left ≡ right
sameReverseTraceDerivationsSameFormula
    Family.restrictionRoot
    Family.restrictionRoot
    refl =
  refl
sameReverseTraceDerivationsSameFormula
    Family.restrictionRoot
    (Family.restrictionFalse right)
    ()
sameReverseTraceDerivationsSameFormula
    Family.restrictionRoot
    (Family.restrictionTrue right)
    ()
sameReverseTraceDerivationsSameFormula
    (Family.restrictionFalse left)
    Family.restrictionRoot
    ()
sameReverseTraceDerivationsSameFormula
    (Family.restrictionTrue left)
    Family.restrictionRoot
    ()
sameReverseTraceDerivationsSameFormula
    (Family.restrictionFalse left)
    (Family.restrictionFalse right)
    refl =
  cong
    (SAT.restrictHead false)
    (sameReverseTraceDerivationsSameFormula left right refl)
sameReverseTraceDerivationsSameFormula
    (Family.restrictionTrue left)
    (Family.restrictionTrue right)
    refl =
  cong
    (SAT.restrictHead true)
    (sameReverseTraceDerivationsSameFormula left right refl)
sameReverseTraceDerivationsSameFormula
    (Family.restrictionFalse left)
    (Family.restrictionTrue right)
    ()
sameReverseTraceDerivationsSameFormula
    (Family.restrictionTrue left)
    (Family.restrictionFalse right)
    ()

traceRepairEqualityImpliesResidualEquality :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (left right :
      Width.LayerNode {root = root} remaining) →
  traceRepair left ≡ traceRepair right →
  Width.LayerResidualEqual left right
traceRepairEqualityImpliesResidualEquality
    {remaining = remaining}
    left
    right
    sameTrace
    with Width.node left | Width.arityExact left
       | Width.node right | Width.arityExact right
... | Family.restriction-node .remaining leftFormula leftDerivation | refl
    | Family.restriction-node .remaining rightFormula rightDerivation | refl =
  λ assignment →
    cong
      (λ formula → SAT.evaluate formula assignment)
      (sameReverseTraceDerivationsSameFormula
        leftDerivation
        rightDerivation
        sameTrace)

------------------------------------------------------------------------
-- Explicit structural size calibration.
------------------------------------------------------------------------

traceTokenCount : List Bool → Nat
traceTokenCount [] =
  zero
traceTokenCount (_ ∷ rest) =
  suc (traceTokenCount rest)

repairStepAddsExactlyOneTraceToken :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (parent :
      Width.LayerNode {root = root} (suc remaining)) →
  traceTokenCount
    (traceRepair (Shannon.layerChild action parent))
  ≡
  suc (traceTokenCount (traceRepair parent))
repairStepAddsExactlyOneTraceToken action parent
    rewrite traceRepairStepExact action parent =
  refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- B1c now has an honest positive baseline:
--
--   * a semantically sufficient repair exists;
--   * its exact Shannon update is one constructor;
--   * its representation grows only by one history token per restriction.
--
-- Therefore repair-cardinality/capacity cannot by itself imply linear
-- generation work.
--
-- What this DOES NOT evade:
--
--   * many different histories may remain semantically distinct;
--   * Q1 still needs distinct final states for distinct residual functions;
--   * the existing stateCount / evaluator-cell charge remains.
--
-- The next meaningful compression question is not whether repair updates can
-- be local -- they can -- but whether distinct histories with equal residual
-- semantics can be canonically merged without first solving the semantic
-- equivalence problem.
------------------------------------------------------------------------
