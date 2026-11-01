module DASHI.Analysis.SetoidAlgebraicAnalyticDerivativeWeldBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

------------------------------------------------------------------------
-- ALGEBRAIC DERIVATIVE NORMAL FORM -> ANALYTIC SETOID DERIVATIVE, BIDI
--
-- A recursively differentiated polynomial expression and an analytic
-- derivative relation may compute the same displayed formula while still being
-- different mathematical objects.  This owner isolates the semantic weld.
------------------------------------------------------------------------

record AlgebraicAnalyticDerivativeProblem : Set₁ where
  field
    R : Spine.SetoidOrderedCompleteReal
    Domain : Set

    function : Domain → Spine.Carrier R
    algebraicDerivative : Domain → Spine.Carrier R

    AnalyticDerivativeAt :
      (Domain → Spine.Carrier R) →
      Domain → Spine.Carrier R → Set

    algebraicConstructionExact : Set
    reading : String

open AlgebraicAnalyticDerivativeProblem public

record AlgebraicAnalyticDerivativeWeld
    (P : AlgebraicAnalyticDerivativeProblem) : Set₁ where
  field
    sameFunctionObject : Set
    sameVariableAndScalarSemantics : Set
    polynomialOperationsRespectSetoidEquality : Set

    analyticDerivativeFromAlgebraicNormalForm :
      ∀ point →
      AnalyticDerivativeAt P
        (function P)
        point
        (algebraicDerivative P point)

    reading : String

open AlgebraicAnalyticDerivativeWeld public

compileAnalyticDerivative :
  ∀ {P} →
  AlgebraicAnalyticDerivativeWeld P →
  ∀ point →
  AnalyticDerivativeAt P
    (function P)
    point
    (algebraicDerivative P point)
compileAnalyticDerivative W = analyticDerivativeFromAlgebraicNormalForm W

------------------------------------------------------------------------
-- Firewalls / cross-pollination.
------------------------------------------------------------------------

data EqualDisplayedDerivativeFormulaAutomaticallyIdentifiesDerivativeSemantics : Set where

data PropositionalPolynomialDerivativeAutomaticallyIsBishopSetoidDerivative : Set where

formulaEqualityDoesNotIdentifyDerivativeNotion :
  EqualDisplayedDerivativeFormulaAutomaticallyIdentifiesDerivativeSemantics → ⊥
formulaEqualityDoesNotIdentifyDerivativeNotion ()

noPropositionalDerivativeReceiptLeak :
  PropositionalPolynomialDerivativeAutomaticallyIsBishopSetoidDerivative → ⊥
noPropositionalDerivativeReceiptLeak ()

record ReverseDerivativeSemanticWeldObligations : Set where
  field
    sameFunctionObject : Set
    sameVariableCarrier : Set
    sameScalarOperations : Set
    analyticDerivativeDefinitionSelected : Set
    algebraicDerivativeProvedToSatisfyThatDefinition : Set

open ReverseDerivativeSemanticWeldObligations public

record Status : Set where
  field
    algebraicAnalyticWeldSurfaceOwned : Bool
    displayedFormulaFirewallOwned : Bool
    concreteBishopAnalyticWeldClosed : Bool

    algebraicAnalyticWeldSurfaceOwnedIsTrue : algebraicAnalyticWeldSurfaceOwned ≡ true
    displayedFormulaFirewallOwnedIsTrue : displayedFormulaFirewallOwned ≡ true
    concreteBishopAnalyticWeldClosedIsFalse : concreteBishopAnalyticWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { algebraicAnalyticWeldSurfaceOwned = true
  ; displayedFormulaFirewallOwned = true
  ; concreteBishopAnalyticWeldClosed = false
  ; algebraicAnalyticWeldSurfaceOwnedIsTrue = refl
  ; displayedFormulaFirewallOwnedIsTrue = refl
  ; concreteBishopAnalyticWeldClosedIsFalse = refl
  }
