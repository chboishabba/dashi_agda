module DASHI.COL where

open import DASHI.Prelude
open import DASHI.OperatorTypes
open import DASHI.LensKernel

------------------------------------------------------------------------
-- Contraction–Obstruction–Lift (COL)
--
-- A generic schema:
--   * within a fixed model class n, an update Kₙ contracts an energy Eₙ
--   * if obstruction holds, a lift ℓₙ : Sₙ → Sₙ₊₁ expands coordinates
--   * after lift, energy can contract again (often strictly)
--
-- This is the common diagram behind:
--   * Fractran: exponent-vector state + rewrite rules + halting obstruction + “add prime / change rule”
--   * Oscillators: fixed basis descent + residual peak obstruction + ADD/NUDGE basis lift
--   * DASHI: kernel contraction + witness/lens obstruction + state-space extension
------------------------------------------------------------------------

-- An indexed family of state spaces.
StateFam : Set₁
StateFam = Nat → Set

-- Energy / cost functional for each level.
EnergyFam : (S : StateFam) → Set₁
EnergyFam S = ∀ n → S n → Nat

-- One-step kernel operator per level.
KernelFam : (S : StateFam) → Set₁
KernelFam S = ∀ n → (S n → S n)

-- Obstruction predicate per level: “model class n cannot reduce further without lift”.
ObsFam : (S : StateFam) → Set₁
ObsFam S = ∀ n → S n → Set

-- Lift map: expands coordinates from n to suc n.
LiftFam : (S : StateFam) → Set₁
LiftFam S = ∀ n → (S n → S (suc n))

------------------------------------------------------------------------
-- Core COL contract bundle

record COL (S : StateFam) : Set₁ where
  field
    E    : EnergyFam S
    K    : KernelFam S
    Obs  : ObsFam S
    lift : LiftFam S

    -- Contraction inside level n: energy does not increase.
    -- (You can strengthen to strict decrease if you have a ranking.)
    contract : ∀ n x → E n (K n x) ≤ E n x

    -- Obstruction is stable under K: if you are obstructed, stepping doesn't “solve” it magically.
    obs-stable : ∀ n x → Obs n x → Obs n (K n x)

    -- Lift is witness-respecting: the old state is embedded, not destroyed.
    -- (Replace with your preferred embedding law.)
    postulate-embed : ∀ n x → ⊤

open COL public

------------------------------------------------------------------------
-- Derived theorem hooks (the “schema theorems”)

-- If not obstructed, repeated contraction gives monotone energy sequence.
iterate : ∀ {A : Set} → (A → A) → Nat → A → A
iterate f zero    x = x
iterate f (suc k) x = iterate f k (f x)

E-monotone-iter :
  ∀ {S} (C : COL S) →
  ∀ n k x →
  COL.E C n (iterate (COL.K C n) k x) ≤ COL.E C n x
E-monotone-iter C n zero    x = ≤-refl
E-monotone-iter C n (suc k) x =
  ≤-trans
    (E-monotone-iter C n k (COL.K C n x))
    (COL.contract C n x)

------------------------------------------------------------------------
-- “Lift enables progress” is NOT provable generically; it’s the key
-- obligation each concrete instance must discharge.
--
-- So we state it as a law: if obstructed at n, there exists a lift target
-- with strictly smaller energy at level (suc n) after some steps.

record LiftProgress {S : StateFam} (C : COL S) : Set₁ where
  field
    progress :
      ∀ n x →
      COL.Obs C n x →
      Σ Nat (λ k →
        COL.E C (suc n) (iterate (COL.K C (suc n)) k (COL.lift C n x))
        < COL.E C (suc n) (COL.lift C n x))

------------------------------------------------------------------------
-- Instantiation notes:
--
-- * Fractran:
--     S n  = exponent vectors (or Nat encoding N)
--     E n  = a ranking like sum of certain exponents
--     K n  = one Fractran step (partial; model stuck as Obs)
--     Obs  = “no fraction applies”
--     lift = extend rule list / add a prime register / widen ontology
--
-- * Oscillators:
--     S n  = n-oscillator parameters (freqs + A/B)
--     E n  = MSE (discretized Nat or use ℚ/ℝ if you add them)
--     K n  = one GD step (or batch step)
--     Obs  = “dominant residual peak > threshold”
--     lift = ADD or NUDGE (basis extension / gauge move)
