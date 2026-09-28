module DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedRejectGuardCommutationExact where

------------------------------------------------------------------------
-- CANONICAL COOK <-> INDEXED REJECT-GUARD COMMUTING SQUARE
--
-- The Cook-level width-preserving reject gadget is
--
--   x_0 OR shift(payload)
--
-- while the indexed Shannon owner uses
--
--   Fin.zero OR liftAboveGuard(cookToIndexed payload).
--
-- This file proves that these are the SAME canonical indexed root, modulo the
-- unavoidable dependent transport identifying their variable counts.
--
-- The proof is deliberately representation-level:
--
--   1. compute the exact canonical variable bound of the Cook gadget;
--   2. decode the indexed guard root back to the same Cook syntax;
--   3. use injectivity of indexedToCook at one fixed arity.
--
-- No SAT oracle, quotient, complexity assumption, or diagonal semantics enters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_⊔_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
import Data.Fin.Properties as FinP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfSpecializationWidthUniversalityNoGoExact as Universal
import DASHI.Mathematics.Complexity.PNotEqualsNPRejectGuardResidualWidthEmbeddingExact as Guard

------------------------------------------------------------------------
-- A tiny max identity used by the shifted-bound induction.
------------------------------------------------------------------------

one : Nat
one = suc zero

oneMaxDistributes :
  (left right : Nat) →
  one ⊔ (left ⊔ right)
  ≡
  (one ⊔ left) ⊔ (one ⊔ right)
oneMaxDistributes zero zero = refl
oneMaxDistributes zero (suc right) = refl
oneMaxDistributes (suc left) zero = refl
oneMaxDistributes (suc left) (suc right) = refl

------------------------------------------------------------------------
-- Adding a fresh guard at zero and shifting every payload variable by one
-- raises the canonical Cook variable bound by exactly one.
------------------------------------------------------------------------

guardedShiftBoundExact :
  (payload : Cook.BooleanFormula) →
  one ⊔
    Bridge.formulaVariableBound
      (Universal.shiftCookFormula payload)
  ≡
  suc (Bridge.formulaVariableBound payload)
guardedShiftBoundExact (Cook.variable index) =
  refl
guardedShiftBoundExact (Cook.constant value) =
  refl
guardedShiftBoundExact (Cook.negate payload) =
  guardedShiftBoundExact payload
guardedShiftBoundExact
    (Cook.conjunction left right)
    rewrite
      oneMaxDistributes
        (Bridge.formulaVariableBound
          (Universal.shiftCookFormula left))
        (Bridge.formulaVariableBound
          (Universal.shiftCookFormula right))
      |
      guardedShiftBoundExact left
      |
      guardedShiftBoundExact right =
  refl
guardedShiftBoundExact
    (Cook.disjunction left right)
    rewrite
      oneMaxDistributes
        (Bridge.formulaVariableBound
          (Universal.shiftCookFormula left))
        (Bridge.formulaVariableBound
          (Universal.shiftCookFormula right))
      |
      guardedShiftBoundExact left
      |
      guardedShiftBoundExact right =
  refl

rejectWidthGadgetVariableBoundExact :
  (payload : Cook.BooleanFormula) →
  Bridge.formulaVariableBound
      (Universal.rejectWidthGadget payload)
  ≡
  suc (Bridge.formulaVariableBound payload)
rejectWidthGadgetVariableBoundExact =
  guardedShiftBoundExact

------------------------------------------------------------------------
-- Decoding the indexed lift increments every Cook variable index by one.
------------------------------------------------------------------------

indexedToCookLiftAboveGuard :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  Bridge.indexedToCook
      (Guard.liftAboveGuard formula)
  ≡
  Universal.shiftCookFormula
      (Bridge.indexedToCook formula)
indexedToCookLiftAboveGuard (SAT.variable index) =
  refl
indexedToCookLiftAboveGuard (SAT.constant value) =
  refl
indexedToCookLiftAboveGuard (SAT.negate formula)
    rewrite indexedToCookLiftAboveGuard formula =
  refl
indexedToCookLiftAboveGuard
    (SAT.conjunction left right)
    rewrite
      indexedToCookLiftAboveGuard left
      |
      indexedToCookLiftAboveGuard right =
  refl
indexedToCookLiftAboveGuard
    (SAT.disjunction left right)
    rewrite
      indexedToCookLiftAboveGuard left
      |
      indexedToCookLiftAboveGuard right =
  refl

indexedRejectGuardDecodesToCookRejectGadget :
  (payload : Cook.BooleanFormula) →
  Bridge.indexedToCook
    (Guard.rejectGuardRoot
      (Bridge.cookToIndexed payload))
  ≡
  Universal.rejectWidthGadget payload
indexedRejectGuardDecodesToCookRejectGadget payload
    rewrite
      indexedToCookLiftAboveGuard
        (Bridge.cookToIndexed payload)
      |
      Bridge.indexedAfterCook payload =
  refl

------------------------------------------------------------------------
-- indexedToCook is injective when the finite arity is fixed.
------------------------------------------------------------------------

cookVariableInjective :
  ∀ {left right : Nat} →
  Cook.variable left ≡ Cook.variable right →
  left ≡ right
cookVariableInjective refl = refl

cookConstantInjective :
  ∀ {left right} →
  Cook.constant left ≡ Cook.constant right →
  left ≡ right
cookConstantInjective refl = refl

cookNegateInjective :
  ∀ {left right} →
  Cook.negate left ≡ Cook.negate right →
  left ≡ right
cookNegateInjective refl = refl

cookConjunctionLeftInjective :
  ∀ {leftA rightA leftB rightB} →
  Cook.conjunction leftA rightA
  ≡
  Cook.conjunction leftB rightB →
  leftA ≡ leftB
cookConjunctionLeftInjective refl = refl

cookConjunctionRightInjective :
  ∀ {leftA rightA leftB rightB} →
  Cook.conjunction leftA rightA
  ≡
  Cook.conjunction leftB rightB →
  rightA ≡ rightB
cookConjunctionRightInjective refl = refl

cookDisjunctionLeftInjective :
  ∀ {leftA rightA leftB rightB} →
  Cook.disjunction leftA rightA
  ≡
  Cook.disjunction leftB rightB →
  leftA ≡ leftB
cookDisjunctionLeftInjective refl = refl

cookDisjunctionRightInjective :
  ∀ {leftA rightA leftB rightB} →
  Cook.disjunction leftA rightA
  ≡
  Cook.disjunction leftB rightB →
  rightA ≡ rightB
cookDisjunctionRightInjective refl = refl

indexedToCookInjective :
  ∀ {variables : Nat}
    (left right : SAT.BooleanFormula variables) →
  Bridge.indexedToCook left
  ≡
  Bridge.indexedToCook right →
  left ≡ right
indexedToCookInjective
    (SAT.variable left)
    (SAT.variable right)
    equality =
  cong SAT.variable
    (FinP.toℕ-injective
      (cookVariableInjective equality))
indexedToCookInjective
    (SAT.variable left)
    (SAT.constant right)
    ()
indexedToCookInjective
    (SAT.variable left)
    (SAT.negate right)
    ()
indexedToCookInjective
    (SAT.variable left)
    (SAT.conjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.variable left)
    (SAT.disjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.constant left)
    (SAT.variable right)
    ()
indexedToCookInjective
    (SAT.constant left)
    (SAT.constant right)
    equality =
  cong SAT.constant
    (cookConstantInjective equality)
indexedToCookInjective
    (SAT.constant left)
    (SAT.negate right)
    ()
indexedToCookInjective
    (SAT.constant left)
    (SAT.conjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.constant left)
    (SAT.disjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.negate left)
    (SAT.variable right)
    ()
indexedToCookInjective
    (SAT.negate left)
    (SAT.constant right)
    ()
indexedToCookInjective
    (SAT.negate left)
    (SAT.negate right)
    equality =
  cong SAT.negate
    (indexedToCookInjective
      left
      right
      (cookNegateInjective equality))
indexedToCookInjective
    (SAT.negate left)
    (SAT.conjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.negate left)
    (SAT.disjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.conjunction leftA leftB)
    (SAT.variable right)
    ()
indexedToCookInjective
    (SAT.conjunction leftA leftB)
    (SAT.constant right)
    ()
indexedToCookInjective
    (SAT.conjunction leftA leftB)
    (SAT.negate right)
    ()
indexedToCookInjective
    (SAT.conjunction leftA leftB)
    (SAT.conjunction rightA rightB)
    equality =
  cong₂ SAT.conjunction
    (indexedToCookInjective
      leftA
      rightA
      (cookConjunctionLeftInjective equality))
    (indexedToCookInjective
      leftB
      rightB
      (cookConjunctionRightInjective equality))
indexedToCookInjective
    (SAT.conjunction leftA leftB)
    (SAT.disjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.disjunction leftA leftB)
    (SAT.variable right)
    ()
indexedToCookInjective
    (SAT.disjunction leftA leftB)
    (SAT.constant right)
    ()
indexedToCookInjective
    (SAT.disjunction leftA leftB)
    (SAT.negate right)
    ()
indexedToCookInjective
    (SAT.disjunction leftA leftB)
    (SAT.conjunction rightA rightB)
    ()
indexedToCookInjective
    (SAT.disjunction leftA leftB)
    (SAT.disjunction rightA rightB)
    equality =
  cong₂ SAT.disjunction
    (indexedToCookInjective
      leftA
      rightA
      (cookDisjunctionLeftInjective equality))
    (indexedToCookInjective
      leftB
      rightB
      (cookDisjunctionRightInjective equality))

------------------------------------------------------------------------
-- Transporting only the phantom arity index does not change Cook decoding.
------------------------------------------------------------------------

indexedToCookSubst :
  ∀ {leftArity rightArity : Nat}
    (arityExact : leftArity ≡ rightArity)
    (formula : SAT.BooleanFormula leftArity) →
  Bridge.indexedToCook
      (subst SAT.BooleanFormula arityExact formula)
  ≡
  Bridge.indexedToCook formula
indexedToCookSubst refl formula =
  refl

------------------------------------------------------------------------
-- Canonical Cook encoding, transported to the obvious successor arity.
------------------------------------------------------------------------

canonicalCookRejectRoot :
  (payload : Cook.BooleanFormula) →
  SAT.BooleanFormula
    (suc (Bridge.formulaVariableBound payload))
canonicalCookRejectRoot payload =
  subst
    SAT.BooleanFormula
    (rejectWidthGadgetVariableBoundExact payload)
    (Bridge.cookToIndexed
      (Universal.rejectWidthGadget payload))

canonicalCookRejectRootDecodes :
  (payload : Cook.BooleanFormula) →
  Bridge.indexedToCook
      (canonicalCookRejectRoot payload)
  ≡
  Universal.rejectWidthGadget payload
canonicalCookRejectRootDecodes payload =
  trans
    (indexedToCookSubst
      (rejectWidthGadgetVariableBoundExact payload)
      (Bridge.cookToIndexed
        (Universal.rejectWidthGadget payload)))
    (Bridge.indexedAfterCook
      (Universal.rejectWidthGadget payload))

------------------------------------------------------------------------
-- MAIN COMMUTING SQUARE.
------------------------------------------------------------------------

cookIndexedRejectGuardCommutes :
  (payload : Cook.BooleanFormula) →
  canonicalCookRejectRoot payload
  ≡
  Guard.rejectGuardRoot
    (Bridge.cookToIndexed payload)
cookIndexedRejectGuardCommutes payload =
  indexedToCookInjective
    (canonicalCookRejectRoot payload)
    (Guard.rejectGuardRoot
      (Bridge.cookToIndexed payload))
    (trans
      (canonicalCookRejectRootDecodes payload)
      (sym
        (indexedRejectGuardDecodesToCookRejectGadget payload)))

------------------------------------------------------------------------
-- Packaged representation theorem: the raw canonical root has the exact
-- successor bound and becomes the indexed guard root after that transport.
------------------------------------------------------------------------

record CookIndexedRejectGuardCommutation
    (payload : Cook.BooleanFormula) : Set where
  constructor cook-indexed-reject-guard-commutation
  field
    variableBoundExact :
      Bridge.formulaVariableBound
          (Universal.rejectWidthGadget payload)
      ≡
      suc (Bridge.formulaVariableBound payload)

    transportedRootExact :
      subst
        SAT.BooleanFormula
        variableBoundExact
        (Bridge.cookToIndexed
          (Universal.rejectWidthGadget payload))
      ≡
      Guard.rejectGuardRoot
        (Bridge.cookToIndexed payload)

open CookIndexedRejectGuardCommutation public

canonicalCookIndexedRejectGuardCommutation :
  (payload : Cook.BooleanFormula) →
  CookIndexedRejectGuardCommutation payload
canonicalCookIndexedRejectGuardCommutation payload =
  cook-indexed-reject-guard-commutation
    (rejectWidthGadgetVariableBoundExact payload)
    (cookIndexedRejectGuardCommutes payload)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The Cook/indexed mismatch is paid.  It is a representation theorem only:
-- whether the ACTUAL all-quotes diagonal compiler emits this Cook gadget under
-- the charged resource/termination discipline remains a separate question.
------------------------------------------------------------------------
