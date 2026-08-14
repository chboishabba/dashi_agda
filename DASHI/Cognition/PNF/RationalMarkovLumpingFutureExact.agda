module DASHI.Cognition.PNF.RationalMarkovLumpingFutureExact where

------------------------------------------------------------------------
-- STOCHASTIC FUTURE QUOTIENT BY MARKOV LUMPING
--
-- A stochastic transition kernel acts on observables through its Markov
-- operator P.  A projection pi is dynamically sufficient when P preserves the
-- subspace of observables that factor through pi.  Instead of assuming function
-- extensionality, the carrier below packages that factorization pointwise and
-- requires each stochastic update to preserve it.
--
-- The resulting theorem is the stochastic analogue of deterministic future
-- congruence: every finite-horizon updated observable remains coarse-factored.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

record FactoredObservable {Fine Coarse : Set}
    (project : Fine → Coarse) : Set₁ where
  constructor factoredObservable
  field
    fineObservable : Fine → ℚ
    coarseObservable : Coarse → ℚ
    factors : (state : Fine) →
      fineObservable state ≡ coarseObservable (project state)

open FactoredObservable public

record ConstructiveMarkovLumping (Fine Coarse : Set) : Set₁ where
  constructor constructiveMarkovLumping
  field
    project : Fine → Coarse
    fineStep : (Fine → ℚ) → Fine → ℚ
    coarseStep : (Coarse → ℚ) → Coarse → ℚ

    preservesFactoredObservable :
      (observable : FactoredObservable project) →
      FactoredObservable project

    preservedFineIsStep :
      (observable : FactoredObservable project) (state : Fine) →
      fineObservable (preservesFactoredObservable observable) state
      ≡ fineStep (fineObservable observable) state

    preservedCoarseIsStep :
      (observable : FactoredObservable project) (coarse : Coarse) →
      coarseObservable (preservesFactoredObservable observable) coarse
      ≡ coarseStep (coarseObservable observable) coarse

open ConstructiveMarkovLumping public

initialFactoredObservable :
  ∀ {Fine Coarse}
    (lumping : ConstructiveMarkovLumping Fine Coarse) →
  (observable : Coarse → ℚ) →
  FactoredObservable (project lumping)
initialFactoredObservable lumping observable =
  factoredObservable
    (λ state → observable (project lumping state))
    observable
    (λ state → refl)

iterateFactored :
  ∀ {Fine Coarse}
    (lumping : ConstructiveMarkovLumping Fine Coarse) →
  Nat → FactoredObservable (project lumping) →
  FactoredObservable (project lumping)
iterateFactored lumping zero observable = observable
iterateFactored lumping (suc n) observable =
  iterateFactored lumping n (preservesFactoredObservable lumping observable)

allFiniteHorizonsRemainCoarseFactored :
  ∀ {Fine Coarse}
    (lumping : ConstructiveMarkovLumping Fine Coarse)
    (horizon : Nat)
    (observable : Coarse → ℚ)
    (state : Fine) →
  fineObservable
    (iterateFactored lumping horizon
      (initialFactoredObservable lumping observable)) state
  ≡ coarseObservable
    (iterateFactored lumping horizon
      (initialFactoredObservable lumping observable))
    (project lumping state)
allFiniteHorizonsRemainCoarseFactored lumping horizon observable state =
  factors
    (iterateFactored lumping horizon
      (initialFactoredObservable lumping observable)) state

------------------------------------------------------------------------
-- One-step commuting square extracted from the proof-carrying operator.
------------------------------------------------------------------------

oneStepMarkovLumping :
  ∀ {Fine Coarse}
    (lumping : ConstructiveMarkovLumping Fine Coarse)
    (observable : Coarse → ℚ)
    (state : Fine) →
  fineStep lumping (λ x → observable (project lumping x)) state
  ≡ coarseStep lumping observable (project lumping state)
oneStepMarkovLumping lumping observable state =
  trans
    (sym (preservedFineIsStep lumping
      (initialFactoredObservable lumping observable) state))
    (trans
      (factors
        (preservesFactoredObservable lumping
          (initialFactoredObservable lumping observable)) state)
      (preservedCoarseIsStep lumping
        (initialFactoredObservable lumping observable)
        (project lumping state)))

------------------------------------------------------------------------
-- Boundary: a concrete stochastic kernel still has to prove positivity,
-- normalization and that aggregation of transition mass over coarse classes
-- implements `preservesFactoredObservable`.  This module proves the general
-- finite-horizon consequence once that lumpability producer is supplied.
------------------------------------------------------------------------
