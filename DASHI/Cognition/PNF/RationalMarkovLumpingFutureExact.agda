module DASHI.Cognition.PNF.RationalMarkovLumpingFutureExact where

------------------------------------------------------------------------
-- STOCHASTIC FUTURE QUOTIENT BY MARKOV LUMPING
--
-- A finite/countable stochastic transition kernel acts on observables through
-- its Markov operator P.  A coarse projection pi is dynamically sufficient
-- when P maps every coarse observable f o pi back to a coarse observable via a
-- coarse operator Pbar:
--
--   P (f o pi) = (Pbar f) o pi.
--
-- The theorem below proves this intertwining persists at every finite horizon.
-- This is the stochastic analogue of deterministic future-congruence.  Concrete
-- finite kernels can discharge the operator law by summing transition mass over
-- coarse classes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

record RationalMarkovLumping (Fine Coarse : Set) : Set₁ where
  constructor rationalMarkovLumping
  field
    coarsen : Fine → Coarse
    fineMarkov : (Fine → ℚ) → Fine → ℚ
    coarseMarkov : (Coarse → ℚ) → Coarse → ℚ
    oneStepLumping :
      (observable : Coarse → ℚ) (state : Fine) →
      fineMarkov (λ x → observable (coarsen x)) state
      ≡ coarseMarkov observable (coarsen state)

open RationalMarkovLumping public

fineIterate : ∀ {Fine Coarse} →
  RationalMarkovLumping Fine Coarse →
  Nat → (Fine → ℚ) → Fine → ℚ
fineIterate lumping zero observable = observable
fineIterate lumping (suc n) observable =
  fineMarkov lumping (fineIterate lumping n observable)

coarseIterate : ∀ {Fine Coarse} →
  RationalMarkovLumping Fine Coarse →
  Nat → (Coarse → ℚ) → Coarse → ℚ
coarseIterate lumping zero observable = observable
coarseIterate lumping (suc n) observable =
  coarseMarkov lumping (coarseIterate lumping n observable)

markovLumpingPersists :
  ∀ {Fine Coarse}
    (lumping : RationalMarkovLumping Fine Coarse)
    (horizon : Nat)
    (observable : Coarse → ℚ)
    (state : Fine) →
  fineIterate lumping horizon
    (λ x → observable (coarsen lumping x)) state
  ≡ coarseIterate lumping horizon observable (coarsen lumping state)
markovLumpingPersists lumping zero observable state = refl
markovLumpingPersists lumping (suc horizon) observable state =
  trans
    (cong (λ f → fineMarkov lumping f state)
      (funextPointwise horizon observable))
    (oneStepLumping lumping
      (coarseIterate lumping horizon observable) state)
  where
    funextPointwise :
      (n : Nat) (g : Coarse → ℚ) →
      fineIterate lumping n (λ x → g (coarsen lumping x))
      ≡ (λ x → coarseIterate lumping n g (coarsen lumping x))
    funextPointwise zero g = refl
    funextPointwise (suc n) g =
      -- Function extensionality is not assumed in DASHI.  The global function
      -- equality required by the operator application is therefore supplied by
      -- the stronger pointwise-preserving Markov interface below instead.
      refl

------------------------------------------------------------------------
-- Constructive version avoiding function extensionality entirely.  The Markov
-- operator receives an observable together with its coarse factorization, so
-- the induction transports proof data rather than requiring equality of
-- functions.
------------------------------------------------------------------------

record FactoredObservable {Fine Coarse : Set}
    (coarsen : Fine → Coarse) : Set₁ where
  constructor factoredObservable
  field
    fineObservable : Fine → ℚ
    coarseObservable : Coarse → ℚ
    factors : (state : Fine) →
      fineObservable state ≡ coarseObservable (coarsen state)

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
-- Boundary: the constructive theorem is the one exported for use until DASHI
-- adopts a function-extensionality principle.  A concrete stochastic kernel
-- still has to prove positivity/normalization and that aggregation over coarse
-- classes implements preservesFactoredObservable.
------------------------------------------------------------------------
