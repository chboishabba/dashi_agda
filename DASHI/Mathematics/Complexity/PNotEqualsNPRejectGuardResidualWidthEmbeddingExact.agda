module DASHI.Mathematics.Complexity.PNotEqualsNPRejectGuardResidualWidthEmbeddingExact where

------------------------------------------------------------------------
-- REJECT-GUARD GADGET PRESERVES AN ARBITRARY SHANNON WIDTH WITNESS
--
-- The self-specialization universality audit already constructs the Cook-level
-- asymmetric reject gadget
--
--   g OR shift(payload)
--
-- which is always satisfiable, while the g=false branch recovers the payload
-- function exactly.
--
-- This owner pays the stronger Shannon statement on the finite indexed carrier:
-- not merely two sample payloads, but EVERY residual-width witness of payload
-- is transported into the false-guard subtree of one guarded root.
--
-- Therefore SAT-polarity compatibility on a rejected quote does not imply any
-- collapse of FutureEquivalent / residual-function width.  Any width-collapse
-- theorem for the actual diagonal family must use more than the fact that the
-- rejected branch is required to be satisfiable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Fin.Base as Fin
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- Shift every payload variable above one fresh guard variable.
------------------------------------------------------------------------

liftAboveGuard :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula (suc variables)
liftAboveGuard (SAT.variable index) =
  SAT.variable (Fin.suc index)
liftAboveGuard (SAT.constant value) =
  SAT.constant value
liftAboveGuard (SAT.negate formula) =
  SAT.negate (liftAboveGuard formula)
liftAboveGuard (SAT.conjunction left right) =
  SAT.conjunction
    (liftAboveGuard left)
    (liftAboveGuard right)
liftAboveGuard (SAT.disjunction left right) =
  SAT.disjunction
    (liftAboveGuard left)
    (liftAboveGuard right)

------------------------------------------------------------------------
-- Restricting the fresh head guard does not alter the shifted payload.
------------------------------------------------------------------------

restrictLiftAboveGuard :
  ∀ {variables : Nat}
    (bit : Bool)
    (formula : SAT.BooleanFormula variables) →
  SAT.restrictHead bit (liftAboveGuard formula)
  ≡ formula
restrictLiftAboveGuard bit (SAT.variable index) =
  refl
restrictLiftAboveGuard bit (SAT.constant value) =
  refl
restrictLiftAboveGuard bit (SAT.negate formula) =
  cong SAT.negate
    (restrictLiftAboveGuard bit formula)
restrictLiftAboveGuard bit (SAT.conjunction left right) =
  cong₂ SAT.conjunction
    (restrictLiftAboveGuard bit left)
    (restrictLiftAboveGuard bit right)
restrictLiftAboveGuard bit (SAT.disjunction left right) =
  cong₂ SAT.disjunction
    (restrictLiftAboveGuard bit left)
    (restrictLiftAboveGuard bit right)

------------------------------------------------------------------------
-- Indexed asymmetric reject gadget.
--
-- This is the Shannon-level analogue of the Cook owner:
--
--   variable 0 OR shifted payload.
------------------------------------------------------------------------

rejectGuardRoot :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula (suc variables)
rejectGuardRoot payload =
  SAT.disjunction
    (SAT.variable Fin.zero)
    (liftAboveGuard payload)

falseWrapped :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula variables
falseWrapped payload =
  SAT.disjunction
    (SAT.constant false)
    payload

rejectGuardFalseChildExact :
  ∀ {variables : Nat}
    (payload : SAT.BooleanFormula variables) →
  SAT.restrictHead false (rejectGuardRoot payload)
  ≡ falseWrapped payload
rejectGuardFalseChildExact payload
    rewrite restrictLiftAboveGuard false payload =
  refl

falseWrappedEvaluation :
  ∀ {variables : Nat}
    (payload : SAT.BooleanFormula variables)
    (assignment : SAT.Assignment variables) →
  SAT.evaluate
    (falseWrapped payload)
    assignment
  ≡
  SAT.evaluate payload assignment
falseWrappedEvaluation payload assignment =
  refl

falseWrappedRestriction :
  ∀ {variables : Nat}
    (bit : Bool)
    (payload : SAT.BooleanFormula (suc variables)) →
  SAT.restrictHead bit (falseWrapped payload)
  ≡
  falseWrapped (SAT.restrictHead bit payload)
falseWrappedRestriction bit payload =
  refl

------------------------------------------------------------------------
-- Replay every payload restriction derivation below the guard=false child.
------------------------------------------------------------------------

guardFalseDerivation :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Family.RestrictionDerivation
    (rejectGuardRoot root)
    (falseWrapped current)
guardFalseDerivation
    {root = root}
    Family.restrictionRoot =
  subst
    (Family.RestrictionDerivation (rejectGuardRoot root))
    (rejectGuardFalseChildExact root)
    (Family.restrictionFalse Family.restrictionRoot)
guardFalseDerivation
    {root = root}
    (Family.restrictionFalse {current = current} derivation) =
  subst
    (Family.RestrictionDerivation (rejectGuardRoot root))
    (falseWrappedRestriction false current)
    (Family.restrictionFalse
      (guardFalseDerivation derivation))
guardFalseDerivation
    {root = root}
    (Family.restrictionTrue {current = current} derivation) =
  subst
    (Family.RestrictionDerivation (rejectGuardRoot root))
    (falseWrappedRestriction true current)
    (Family.restrictionTrue
      (guardFalseDerivation derivation))

------------------------------------------------------------------------
-- Reachable same-layer nodes transport without changing remaining arity.
------------------------------------------------------------------------

guardFalseLayerNode :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.LayerNode {root = root} remaining →
  Width.LayerNode
    {root = rejectGuardRoot root}
    remaining
guardFalseLayerNode source =
  Width.layer-node
    (Family.restriction-node
      (Family.currentVariables
        (Width.node source))
      (falseWrapped
        (Family.currentFormula
          (Width.node source)))
      (guardFalseDerivation
        (Family.derivation
          (Width.node source))))
    (Width.arityExact source)

------------------------------------------------------------------------
-- Equality of wrapped residual functions implies equality of the payload
-- residual functions, because false OR x = x pointwise.
------------------------------------------------------------------------

guardFalseResidualEqualityReflects :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (left right : Width.LayerNode {root = root} remaining) →
  Width.LayerResidualEqual
    (guardFalseLayerNode left)
    (guardFalseLayerNode right) →
  Width.LayerResidualEqual left right
guardFalseResidualEqualityReflects
    left right wrappedEqual assignment
    with Width.arityExact left
       | Width.arityExact right
... | refl | refl =
  trans
    (sym
      (falseWrappedEvaluation
        (Family.currentFormula
          (Width.node left))
        assignment))
    (trans
      (wrappedEqual assignment)
      (falseWrappedEvaluation
        (Family.currentFormula
          (Width.node right))
        assignment))

------------------------------------------------------------------------
-- Main width-preserving embedding.
------------------------------------------------------------------------

rejectGuardPreservesResidualWidthWitness :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Width.ResidualWidthWitness
    {root = root}
    remaining
    width →
  Width.ResidualWidthWitness
    {root = rejectGuardRoot root}
    remaining
    width
rejectGuardPreservesResidualWidthWitness witness =
  Width.residual-width-witness
    (λ index →
      guardFalseLayerNode
        (Width.representative witness index))
    (λ {left} {right} wrappedEqual →
      Width.residualEqualIndicesEqual witness
        (guardFalseResidualEqualityReflects
          (Width.representative witness left)
          (Width.representative witness right)
          wrappedEqual))

------------------------------------------------------------------------
-- Consequently every honest Q1 quotient of the guarded root must retain at
-- least the payload witness width.
------------------------------------------------------------------------

rejectGuardWidthBelowQ1StateCount :
  ∀ {rootVariables remaining width : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient :
      Quotient.RestrictionSemanticQuotient
        (rejectGuardRoot root)) →
  Width.ResidualWidthWitness
    {root = root}
    remaining
    width →
  width ≤ Quotient.stateCount quotient
rejectGuardWidthBelowQ1StateCount quotient witness =
  Width.residualWidthBelowQ1StateCount
    quotient
    (rejectGuardPreservesResidualWidthWitness witness)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- For any payload root with a width-w residual layer, one fresh reject guard
-- produces a SAT-compatible branch whose Shannon family still has width w.
--
-- Hence:
--
--   rejected-quote SAT polarity
--       DOES NOT
--   force small residual width.
--
-- A genuine width restriction for the full self-diagonal body must therefore
-- exploit quote dependence / all-quotes compilation / resource accounting or a
-- stronger structural law of the specific body.  Polarity alone is exhausted.
------------------------------------------------------------------------
