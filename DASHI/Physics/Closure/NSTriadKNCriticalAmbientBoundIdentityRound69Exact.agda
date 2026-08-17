module DASHI.Physics.Closure.NSTriadKNCriticalAmbientBoundIdentityRound69Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Escauriaza; Gregory Seregin; Vladimir Sverak.
-- Title: "L3,infinity-solutions of the Navier-Stokes equations and backward
-- uniqueness".
-- DOI: 10.1070/RM2003v058n02ABEH000609.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 69 / CONDITIONAL-ROUTE CIRCULARITY BOUNDARY
--
-- The quantitative ESS/Tao/Barker-Prange machinery is extremely relevant as
-- a propagation architecture, but its ambient critical hypothesis cannot be
-- used as the producer for DASHI C1.  On the repository's canonical critical
-- ratio, the abstract ambient hypothesis
--
--      forall n, Xi_n <= K
--
-- is literally the same proposition as the Round63 C1 target.
--
-- The identity below is deliberately simple: it prevents later adapters from
-- renaming the C1 target "Type-I control", "ambient critical control" or
-- "regularity epoch authority" and then importing it as if it were a weaker
-- premise.  Any propagation theorem consuming this type remains conditional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1

AmbientCriticalBound :
  ∀ {balances block} →
  C1.PositiveCriticalBlockScale balances block →
  ℚ → Set
AmbientCriticalBound positiveBlock K =
  (n : Nat) → C1.normalizedCriticalRatio positiveBlock n ≤ K

UniformCriticalRatioBound :
  ∀ {balances block} →
  C1.PositiveCriticalBlockScale balances block →
  ℚ → Set
UniformCriticalRatioBound positiveBlock K =
  (n : Nat) → C1.normalizedCriticalRatio positiveBlock n ≤ K

ambientCriticalBoundIsUniformCriticalRatioBound :
  ∀ {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block)
    (K : ℚ) →
  AmbientCriticalBound positiveBlock K →
  UniformCriticalRatioBound positiveBlock K
ambientCriticalBoundIsUniformCriticalRatioBound positiveBlock K bound = bound

uniformCriticalRatioBoundIsAmbientCriticalBound :
  ∀ {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block)
    (K : ℚ) →
  UniformCriticalRatioBound positiveBlock K →
  AmbientCriticalBound positiveBlock K
uniformCriticalRatioBoundIsAmbientCriticalBound positiveBlock K bound = bound

record ConditionalCriticalPropagation
    {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block)
    (K : ℚ)
    (ConcentrationConclusion : Set) : Set where
  field
    propagateFromAmbientCriticalBound :
      AmbientCriticalBound positiveBlock K → ConcentrationConclusion

open ConditionalCriticalPropagation public

-- Such a conditional propagation theorem may be valuable after C1 is known,
-- but the type itself supplies no constructor for the ambient bound.
conditionalPropagationConsumesC1Target :
  ∀ {balances block K ConcentrationConclusion}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block} →
  ConditionalCriticalPropagation positiveBlock K ConcentrationConclusion →
  UniformCriticalRatioBound positiveBlock K →
  ConcentrationConclusion
conditionalPropagationConsumesC1Target propagation c1 =
  propagateFromAmbientCriticalBound propagation
    (uniformCriticalRatioBoundIsAmbientCriticalBound _ _ c1)

round69AmbientCriticalHypothesisIsExactlyC1 : Bool
round69AmbientCriticalHypothesisIsExactlyC1 = true

round69ConditionalPropagationIsUnconditionalC1Producer : Bool
round69ConditionalPropagationIsUnconditionalC1Producer = false

round69AmbientCriticalHypothesisIsExactlyC1IsTrue :
  round69AmbientCriticalHypothesisIsExactlyC1 ≡ true
round69AmbientCriticalHypothesisIsExactlyC1IsTrue = refl

round69ConditionalPropagationIsUnconditionalC1ProducerIsFalse :
  round69ConditionalPropagationIsUnconditionalC1Producer ≡ false
round69ConditionalPropagationIsUnconditionalC1ProducerIsFalse = refl
