module DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact where

------------------------------------------------------------------------
-- STRICTLY SMALLER SEMANTIC REPRESENTATIVES FOR A ROOT-SCOPED QUOTIENT
--
-- A non-circular way to exploit the hypothetical SAT decider is to call it
-- only on STRICTLY SMALLER formulas.
--
-- Strengthen a root-scoped restriction quotient with one ordinary Cook formula
-- representative for each quotient state:
--
--   representative : State -> Cook.BooleanFormula
--
-- such that every reachable restricted node is equisatisfiable with the
-- representative of its state, and every representative is strictly smaller
-- than the Cook syntax of the root.
--
-- Main theorem under SAT in P:
--
--   D(indexedToCook current)
--     =
--   D(representative(classify current)).
--
-- Thus the quotient turns same-size Shannon descendants into smaller semantic
-- queries.  This is a concrete resource-bounded route that does NOT require a
-- finite quotation of D itself.
--
-- The missing theorem is constructing such representatives for the special
-- self-diagonal family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Cook-level equisatisfiability.
------------------------------------------------------------------------

CookSatisfiabilityEquivalent :
  Cook.BooleanFormula →
  Cook.BooleanFormula →
  Set
CookSatisfiabilityEquivalent left right =
  (Cook.Satisfiable left → Cook.Satisfiable right)
  ×
  (Cook.Satisfiable right → Cook.Satisfiable left)

------------------------------------------------------------------------
-- Quotient plus strictly smaller representatives.
------------------------------------------------------------------------

record StrictSemanticRepresentativeQuotient
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor strict-semantic-representative-quotient
  field
    quotient :
      Quotient.RestrictionSemanticQuotient root

    representative :
      Fin (Quotient.stateCount quotient) →
      Cook.BooleanFormula

    representativeEquivalent :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables}
        (derivation :
          Family.RestrictionDerivation root current) →
      CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (representative
          (Quotient.classify quotient derivation))

    representativeStrictlySmallerThanRoot :
      (state : Fin (Quotient.stateCount quotient)) →
      Size.formulaNodeCount
        (representative state)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

open StrictSemanticRepresentativeQuotient public

------------------------------------------------------------------------
-- Exact SAT decision agrees with the smaller representative.
------------------------------------------------------------------------

representativeDecisionEqualsReachableDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      StrictSemanticRepresentativeQuotient root)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables}
    (derivation :
      Family.RestrictionDerivation root current) →
  PR.decide satP
    (Bridge.indexedToCook current)
  ≡
  PR.decide satP
    (representative strictQuotient
      (Quotient.classify
        (quotient strictQuotient)
        derivation))
representativeDecisionEqualsReachableDecision
    satP
    strictQuotient
    {current = current}
    derivation
    with PR.decide satP
           (Bridge.indexedToCook current)
       | PR.decide satP
           (representative strictQuotient
             (Quotient.classify
               (quotient strictQuotient)
               derivation))
... | true | true =
  refl
... | false | false =
  refl
... | true | false =
  falseNotTrue
    (PR.complete
      satP
      representativeFormula
      (proj₁ equivalent
        (PR.sound
          satP
          (Bridge.indexedToCook current)
          refl)))
  where
    representativeFormula :
      Cook.BooleanFormula
    representativeFormula =
      representative strictQuotient
        (Quotient.classify
          (quotient strictQuotient)
          derivation)

    equivalent :
      CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        representativeFormula
    equivalent =
      representativeEquivalent
        strictQuotient
        derivation
... | false | true =
  falseNotTrue
    (PR.complete
      satP
      (Bridge.indexedToCook current)
      (proj₂ equivalent
        (PR.sound
          satP
          representativeFormula
          refl)))
  where
    representativeFormula :
      Cook.BooleanFormula
    representativeFormula =
      representative strictQuotient
        (Quotient.classify
          (quotient strictQuotient)
          derivation)

    equivalent :
      CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        representativeFormula
    equivalent =
      representativeEquivalent
        strictQuotient
        derivation

------------------------------------------------------------------------
-- Root specialization: exact strict semantic descent.
------------------------------------------------------------------------

rootDecisionStrictlyDescends :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      StrictSemanticRepresentativeQuotient root) →
  PR.decide satP
    (Bridge.indexedToCook root)
  ≡
  PR.decide satP
    (representative strictQuotient
      (Quotient.classify
        (quotient strictQuotient)
        Family.restrictionRoot))
rootDecisionStrictlyDescends satP strictQuotient =
  representativeDecisionEqualsReachableDecision
    satP
    strictQuotient
    Family.restrictionRoot

rootRepresentativeIsStrictlySmaller :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      StrictSemanticRepresentativeQuotient root) →
  Size.formulaNodeCount
    (representative strictQuotient
      (Quotient.classify
        (quotient strictQuotient)
        Family.restrictionRoot))
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook root)
rootRepresentativeIsStrictlySmaller strictQuotient =
  representativeStrictlySmallerThanRoot
    strictQuotient
    (Quotient.classify
      (quotient strictQuotient)
      Family.restrictionRoot)

------------------------------------------------------------------------
-- Research consequence.
--
-- This is a sharper P9 target than "small quotient image":
--
--   reachable restricted node
--       -> quotient state
--       -> strictly smaller equisatisfiable representative.
--
-- Under the contradiction hypothesis, D may safely be invoked on that smaller
-- representative to recover the target decision.  The call is no longer a
-- same-size circular invocation.
--
-- Constructing this strict representative quotient for the generated
-- self-diagonal family remains OPEN and would be genuine new mathematics.
------------------------------------------------------------------------
