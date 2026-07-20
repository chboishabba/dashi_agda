{-# OPTIONS --safe #-}
module DASHI.Core.BasinFiniteDescent where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Properties as NatP
open import Data.Sum using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Basin-local descent.
--
-- Global contraction is usually too strong for a branching multiscale system.
-- The correct reusable statement is local: inside an admissible basin, either
-- the state is fixed or the selected action strictly decreases.

record BasinStrictDescent (S : Set) : Set₁ where
  field
    step : S → S
    Basin : S → Set
    Fixed : S → Set
    cost : S → Nat
    fixed-sound : ∀ {x} → Fixed x → step x ≡ x
    preserves-basin : ∀ {x} → Basin x → Basin (step x)
    strict-or-fixed :
      ∀ {x} → Basin x →
      cost (step x) < cost x ⊎ Fixed x
open BasinStrictDescent public

record DescentStep
  {S : Set}
  (D : BasinStrictDescent S)
  (x : S) : Set where
  field
    in-basin : Basin D x
    next-in-basin : Basin D (step D x)
    progress : cost D (step D x) < cost D x ⊎ Fixed D x
open DescentStep public

make-descent-step :
  ∀ {S} (D : BasinStrictDescent S) (x : S) →
  Basin D x → DescentStep D x
make-descent-step D x bx =
  record
    { in-basin = bx
    ; next-in-basin = preserves-basin D bx
    ; progress = strict-or-fixed D bx
    }

------------------------------------------------------------------------
-- A finite witness is deliberately explicit.  It certifies a concrete run
-- rather than pretending that non-expansion alone implies convergence.

record FiniteDescentWitness
  {S : Set}
  (D : BasinStrictDescent S)
  (start : S) : Set where
  field
    endpoint : S
    steps : Nat
    endpoint-in-basin : Basin D endpoint
    endpoint-fixed : Fixed D endpoint
    endpoint-fixed-sound : step D endpoint ≡ endpoint
    endpoint-cost-bounded : cost D endpoint ≤ cost D start
open FiniteDescentWitness public

------------------------------------------------------------------------
-- Canonical inhabited example: natural-number countdown.

countdown : Nat → Nat
countdown zero = zero
countdown (suc n) = n

CountdownFixed : Nat → Set
CountdownFixed n = n ≡ zero

countdown-fixed-sound : ∀ {n} → CountdownFixed n → countdown n ≡ n
countdown-fixed-sound {zero} refl = refl

countdown-strict-or-fixed :
  ∀ {n} → countdown n < n ⊎ CountdownFixed n
countdown-strict-or-fixed {zero} = inj₂ refl
countdown-strict-or-fixed {suc n} = inj₁ (NatP.n<1+n n)

countdownDescent : BasinStrictDescent Nat
countdownDescent =
  record
    { step = countdown
    ; Basin = λ _ → Nat
    ; Fixed = CountdownFixed
    ; cost = λ n → n
    ; fixed-sound = countdown-fixed-sound
    ; preserves-basin = λ {_} _ → zero
    ; strict-or-fixed = λ {_} _ → countdown-strict-or-fixed
    }

countdown-zero-witness : FiniteDescentWitness countdownDescent zero
countdown-zero-witness =
  record
    { endpoint = zero
    ; steps = zero
    ; endpoint-in-basin = zero
    ; endpoint-fixed = refl
    ; endpoint-fixed-sound = refl
    ; endpoint-cost-bounded = NatP.≤-refl
    }
