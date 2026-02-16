module Fascism_Tests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma using (Σ; _,_)

open import FascisticSystem
open import AntiFascistSystem
-- Smoke tests: current interfaces and postulated theorems remain callable.

postulate
  sF : FascisticSystem.S
  uA : AntiFascistSystem.Invertible
  sA : AntiFascistSystem.S

fascism-monotone-smoke = FascisticSystem.monotone sF

fascism-strict-decrease-smoke = FascisticSystem.strict-decrease sF

anti-entropy-preserved-smoke = AntiFascistSystem.entropy-preserved uA sA

anti-non-collapse-smoke = AntiFascistSystem.non-collapse uA

-- Interface-level comparison hook to quantum: unitary evolution should be invertible,
-- so it cannot satisfy the projection-only + strict contraction hypotheses simultaneously.
-- We keep this as a spec-level test (type only).

postulate
  QState : Set
  UQ : QState → QState

unitary-is-invertible : Set
unitary-is-invertible = Σ (QState → QState) (λ inv → (∀ x → inv (UQ x) ≡ x) × (∀ x → UQ (inv x) ≡ x))
  where
    infixr 4 _×_
    record _×_ (A B : Set) : Set where
      constructor _,_
      field fst : A
            snd : B
