module DASHI.Reasoning.NonginRecursiveObserverDepthTowerExact where

------------------------------------------------------------------------
-- NONGIN RECURSIVE OBSERVER DEPTH TOWER
--
-- The raw Nongin syntax permits O(x), O(O(x)), ... .  This owner supplies the
-- additional semantic structure needed to interpret finite observer nesting as
-- a depth-indexed inverse system: one-step truncation, exact residual-assisted
-- reopening, and a bridge from the historical ObserverTerm syntax.
--
-- Syntax and semantic depth are deliberately not identified by fiat.  The
-- bridge below is an explicit translation into an independently structured
-- DepthPresheaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Foundations.RelationalDepthPresheafExact as Depth
import DASHI.Philosophy.NonginOriginFormalizationExact as Origin

------------------------------------------------------------------------
-- Depth-indexed observer states.
------------------------------------------------------------------------

data ObserverDepthState (Observer X : Set) : Nat → Set where
  depthZero : X → ObserverDepthState Observer X zero
  depthStep :
    {depth : Nat} →
    Observer →
    ObserverDepthState Observer X depth →
    ObserverDepthState Observer X (suc depth)

truncateOne :
  ∀ {Observer X : Set} {depth : Nat} →
  ObserverDepthState Observer X (suc depth) →
  ObserverDepthState Observer X depth
truncateOne (depthStep observer prior) = prior

observerDepthPresheaf :
  ∀ {Observer X : Set} →
  Depth.DepthPresheaf (ObserverDepthState Observer X)
observerDepthPresheaf = record { truncate = λ depth state → truncateOne state }

truncateToBase :
  ∀ {Observer X : Set} {depth : Nat} →
  ObserverDepthState Observer X depth →
  ObserverDepthState Observer X zero
truncateToBase (depthZero x) = depthZero x
truncateToBase (depthStep observer prior) = truncateToBase prior

truncateToBaseAfterOne :
  ∀ {Observer X : Set} {depth : Nat}
    (fine : ObserverDepthState Observer X (suc depth)) →
  truncateToBase fine ≡ truncateToBase (truncateOne fine)
truncateToBaseAfterOne (depthStep observer prior) = refl

------------------------------------------------------------------------
-- The information removed by one restriction is retained as a residual.
------------------------------------------------------------------------

OneStepResidual :
  ∀ {Observer X : Set} {depth : Nat} →
  ObserverDepthState Observer X depth → Set
OneStepResidual {Observer = Observer} coarse = Observer

residualOfFine :
  ∀ {Observer X : Set} {depth : Nat}
    (fine : ObserverDepthState Observer X (suc depth)) →
  OneStepResidual (truncateOne fine)
residualOfFine (depthStep observer prior) = observer

reopenOne :
  ∀ {Observer X : Set} {depth : Nat}
    (coarse : ObserverDepthState Observer X depth) →
  OneStepResidual coarse →
  ObserverDepthState Observer X (suc depth)
reopenOne coarse observer = depthStep observer coarse

reopenOneExact :
  ∀ {Observer X : Set} {depth : Nat}
    (fine : ObserverDepthState Observer X (suc depth)) →
  reopenOne (truncateOne fine) (residualOfFine fine) ≡ fine
reopenOneExact (depthStep observer prior) = refl

------------------------------------------------------------------------
-- Bridge from the historical recursive syntax.
------------------------------------------------------------------------

observerTermDepth :
  ∀ {Observer X : Set} →
  Origin.ObserverTerm Observer X → Nat
observerTermDepth (Origin.observed x) = zero
observerTermDepth (Origin.observes observer term) = suc (observerTermDepth term)

observerTermToDepthState :
  ∀ {Observer X : Set}
    (term : Origin.ObserverTerm Observer X) →
  ObserverDepthState Observer X (observerTermDepth term)
observerTermToDepthState (Origin.observed x) = depthZero x
observerTermToDepthState (Origin.observes observer term) =
  depthStep observer (observerTermToDepthState term)

observedHasDepthZero :
  ∀ {Observer X : Set} (x : X) →
  observerTermDepth (Origin.observed x) ≡ zero
observedHasDepthZero x = refl

observesAddsOneDepth :
  ∀ {Observer X : Set}
    (observer : Observer)
    (term : Origin.ObserverTerm Observer X) →
  observerTermDepth (Origin.observes observer term)
  ≡ suc (observerTermDepth term)
observesAddsOneDepth observer term = refl

------------------------------------------------------------------------
-- Canonical collision/reopening fixture.
------------------------------------------------------------------------

canonicalBase : ObserverDepthState Origin.Bit Origin.Bit zero
canonicalBase = depthZero Origin.bit0

canonicalFineLeft : ObserverDepthState Origin.Bit Origin.Bit (suc zero)
canonicalFineLeft = depthStep Origin.bit0 canonicalBase

canonicalFineRight : ObserverDepthState Origin.Bit Origin.Bit (suc zero)
canonicalFineRight = depthStep Origin.bit1 canonicalBase

canonicalFineStatesCollideAfterTruncation :
  truncateOne canonicalFineLeft ≡ truncateOne canonicalFineRight
canonicalFineStatesCollideAfterTruncation = refl

canonicalFineStatesRemainDistinct :
  canonicalFineLeft ≡ canonicalFineRight → ⊥
canonicalFineStatesRemainDistinct ()

canonicalLeftReopensExactly :
  reopenOne
    (truncateOne canonicalFineLeft)
    (residualOfFine canonicalFineLeft)
  ≡ canonicalFineLeft
canonicalLeftReopensExactly = reopenOneExact canonicalFineLeft

canonicalRightReopensExactly :
  reopenOne
    (truncateOne canonicalFineRight)
    (residualOfFine canonicalFineRight)
  ≡ canonicalFineRight
canonicalRightReopensExactly = reopenOneExact canonicalFineRight

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

data ObserverSyntaxDefinitionallyEqualsDepthSemantics : Set where

syntaxDoesNotCreateDepthSemanticsByItself :
  ObserverSyntaxDefinitionallyEqualsDepthSemantics → ⊥
syntaxDoesNotCreateDepthSemanticsByItself ()

record NonginRecursiveObserverDepthTowerBoundary : Set where
  constructor nongin-recursive-observer-depth-tower-boundary
  field
    depthPresheafPaid : Bool
    coarseCollisionPaid : Bool
    residualReopeningPaid : Bool
    observerTermBridgePaid : Bool
    syntaxEqualsDepthSemantics : Bool
    residualClaimedMinimalOrUnique : Bool
    pAdicPsychologicalMetricPromoted : Bool

open NonginRecursiveObserverDepthTowerBoundary public

canonicalNonginRecursiveObserverDepthTowerBoundary :
  NonginRecursiveObserverDepthTowerBoundary
canonicalNonginRecursiveObserverDepthTowerBoundary =
  nongin-recursive-observer-depth-tower-boundary
    true
    true
    true
    true
    false
    false
    false
