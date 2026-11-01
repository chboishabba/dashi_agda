module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientClassSelectionAlgorithmExact where

------------------------------------------------------------------------
-- EXECUTABLE SAT-BLIND CLASS SELECTION FROM A QUOTIENT TRANSITION TABLE
--
-- Once a root-scoped quotient table exists, the class of any reachable
-- Shannon restriction node can be computed by replaying the restriction path
-- through the quotient step function.
--
-- This is an actual structurally recursive selector.  Its execution path is
-- the list of quotient states visited during replay, and the repository's
-- transition-count consumer measures that path exactly by restriction depth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- Restriction depth.
------------------------------------------------------------------------

restrictionDepth :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Nat
restrictionDepth Family.restrictionRoot =
  zero
restrictionDepth (Family.restrictionFalse derivation) =
  suc (restrictionDepth derivation)
restrictionDepth (Family.restrictionTrue derivation) =
  suc (restrictionDepth derivation)

------------------------------------------------------------------------
-- Executable selector.
------------------------------------------------------------------------

selectClass :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Fin (Quotient.stateCount quotient)
selectClass quotient Family.restrictionRoot =
  Quotient.classify quotient Family.restrictionRoot
selectClass quotient (Family.restrictionFalse derivation) =
  Quotient.step quotient
    (selectClass quotient derivation)
    false
selectClass quotient (Family.restrictionTrue derivation) =
  Quotient.step quotient
    (selectClass quotient derivation)
    true

------------------------------------------------------------------------
-- Exactness against the quotient's semantic classifier.
------------------------------------------------------------------------

selectClassExact :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  selectClass quotient derivation
  ≡
  Quotient.classify quotient derivation
selectClassExact quotient Family.restrictionRoot =
  refl
selectClassExact quotient
    (Family.restrictionFalse derivation) =
  trans
    (cong
      (λ state → Quotient.step quotient state false)
      (selectClassExact quotient derivation))
    (sym
      (Quotient.falseStepCompatible
        quotient
        derivation))
selectClassExact quotient
    (Family.restrictionTrue derivation) =
  trans
    (cong
      (λ state → Quotient.step quotient state true)
      (selectClassExact quotient derivation))
    (sym
      (Quotient.trueStepCompatible
        quotient
        derivation))

------------------------------------------------------------------------
-- Actual execution path.
--
-- Reverse chronological order makes transition counting structurally exact:
-- each restriction constructor contributes one path transition.
------------------------------------------------------------------------

selectionTrace :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  List (Fin (Quotient.stateCount quotient))
selectionTrace quotient Family.restrictionRoot =
  selectClass quotient Family.restrictionRoot ∷ []
selectionTrace quotient
    (Family.restrictionFalse derivation) =
  selectClass quotient
      (Family.restrictionFalse derivation)
  ∷
  selectionTrace quotient derivation
selectionTrace quotient
    (Family.restrictionTrue derivation) =
  selectClass quotient
      (Family.restrictionTrue derivation)
  ∷
  selectionTrace quotient derivation

selectionPath :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Complexity.ExecutionFibrePath
    (Fin (Quotient.stateCount quotient))
selectionPath quotient derivation =
  Complexity.executionFibrePath
    (selectionTrace quotient derivation)

------------------------------------------------------------------------
-- Exact operational discovery cost of selecting a reachable class.
------------------------------------------------------------------------

selectionTransitionCostExact :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  Complexity.K
    Complexity.transitionConsumer
    (selectionPath quotient derivation)
  ≡
  restrictionDepth derivation
selectionTransitionCostExact quotient Family.restrictionRoot =
  refl
selectionTransitionCostExact quotient
    (Family.restrictionFalse derivation)
    rewrite
      selectionTransitionCostExact quotient derivation =
  refl
selectionTransitionCostExact quotient
    (Family.restrictionTrue derivation)
    rewrite
      selectionTransitionCostExact quotient derivation =
  refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Once the transition table and root class exist:
--
--   reachable class selection is SAT-blind
--   and costs exactly restriction depth
--
-- under the repository's actual path-transition cost consumer.
--
-- Therefore class selection itself is not the remaining Clay breakthrough.
-- The unresolved construction is upstream:
--
--   build the root class + transition table + closed representative chains
--   SAT-blindly, with the actual construction execution cost fitting the
--   charged descent margin.
------------------------------------------------------------------------
