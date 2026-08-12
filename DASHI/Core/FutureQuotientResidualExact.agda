module DASHI.Core.FutureQuotientResidualExact where

------------------------------------------------------------------------
-- RESIDUALS RELATIVE TO THE CANONICAL FUTURE QUOTIENT
--
-- FutureObservationLanguageQuotientExact identifies the largest relation that
-- may be collapsed without changing the consumer-visible future language.
-- This module answers the complementary question: what extra receipt must be
-- retained if an application later wants to reopen a representative?
--
-- Exact reopening and future-relevant reopening are deliberately separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Exact residual over a presented future quotient.
------------------------------------------------------------------------

record ExactResidualOverFutureQuotient
    {State Action Observation : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    (presentation : Future.FutureEquivalencePresentation system project)
    : Set₁ where
  constructor exactResidualOverFutureQuotient
  field
    Residual : Set
    residual : State → Residual
    reopen : Future.QuotientCode presentation → Residual → State
    reopenExact :
      (state : State) →
      reopen
        (Future.classOf presentation state)
        (residual state)
      ≡ state

open ExactResidualOverFutureQuotient public

------------------------------------------------------------------------
-- The quotient class together with an exact residual is injective.
------------------------------------------------------------------------

classAndResidualDetermineState :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project}
    (receipt : ExactResidualOverFutureQuotient presentation)
    {left right : State} →
  Future.classOf presentation left ≡ Future.classOf presentation right →
  residual receipt left ≡ residual receipt right →
  left ≡ right
classAndResidualDetermineState receipt classEqual residualEqual =
  transEq
    (symEq (reopenExact receipt _))
    (transEq
      (cong₂Eq (reopen receipt) classEqual residualEqual)
      (reopenExact receipt _))
  where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

    transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    transEq refl refl = refl

    cong₂Eq :
      ∀ {A B C : Set} (f : A → B → C)
        {a a′ : A} {b b′ : B} →
      a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
    cong₂Eq f refl refl = refl

------------------------------------------------------------------------
-- Future-relevant reopening is weaker: reopening may choose any state in the
-- same canonical future-equivalence class.
------------------------------------------------------------------------

record RelevantResidualOverFutureQuotient
    {State Action Observation : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    (presentation : Future.FutureEquivalencePresentation system project)
    : Set₁ where
  constructor relevantResidualOverFutureQuotient
  field
    Residual : Set
    residual : State → Residual
    reopen : Future.QuotientCode presentation → Residual → State
    reopenRelevant :
      (state : State) →
      Future.FutureObservationEquivalent system project
        (reopen
          (Future.classOf presentation state)
          (residual state))
        state

open RelevantResidualOverFutureQuotient public

exactResidualIsRelevant :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {presentation : Future.FutureEquivalencePresentation system project} →
  ExactResidualOverFutureQuotient presentation →
  RelevantResidualOverFutureQuotient presentation
exactResidualIsRelevant {presentation = presentation} exact =
  relevantResidualOverFutureQuotient
    (Residual exact)
    (residual exact)
    (reopen exact)
    λ state →
      transportFuture
        (reopenExact exact state)
        (Future.futureEquivalentRefl state)
  where
    transportFuture :
      ∀ {State Action Observation}
        {system : Dependency.DependentActionSystem State Action}
        {project : State → Observation}
        {left right : State} →
      left ≡ right →
      Future.FutureObservationEquivalent system project right right →
      Future.FutureObservationEquivalent system project left right
    transportFuture refl witness = witness

------------------------------------------------------------------------
-- Boundary: the future quotient is canonical at the relation level; residual
-- cardinality/description length is an additional application-level
-- optimization problem and is not inferred from quotient safety alone.
------------------------------------------------------------------------
