module DASHI.Geometry.ProjectionContractionOrthogonalityTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Product public using (_×_)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Context for the test harness (no postulates; all fields are explicit).
------------------------------------------------------------------------

record TestContext : Set₁ where
  field
    S   : Set
    _S+_ : S → S → S
    _S-_ : S → S → S
    0#  : S

    -- Group-ish laws you’ll need for “detail = x - P x” reasoning
    +-assoc : ∀ x y z → (x S+ y) S+ z ≡ x S+ (y S+ z)
    +-idʳ   : ∀ x → x S+ 0# ≡ x
    +-idˡ   : ∀ x → 0# S+ x ≡ x
    +-invʳ  : ∀ x → x S- x ≡ 0#

    -- Metric / norm interface (kept abstract; later bind to your induced norm)
    dist : S → S → Set

    -- A “norm” is distance to 0. (You can swap this for your actual norm.)
    ∥_∥ : S → Set
    ∥x∥-def : ∀ x → ∥ x ∥ ≡ dist x 0#


------------------------------------------------------------------------
-- Recognisable lift decomposition (your “telescoping identity”)
------------------------------------------------------------------------

record RecognisableLift {C : TestContext} (P : TestContext.S C → TestContext.S C) : Set where
  open TestContext C renaming (S to S₀; _S+_ to _+_; _S-_ to _-_; 0# to 0#)
  field
    -- every x decomposes uniquely into coarse + detail:
    coarse   : S₀ → S₀
    detail   : S₀ → S₀
    split    : ∀ x → x ≡ coarse x + detail x

    -- recognisable uniqueness: if x = c+d = c'+d' with both c,c' fixed by P
    -- and both d,d' in the fiber kernel, then equal (abstracted)
    uniq :
      ∀ x c d c' d' →
      x ≡ c + d →
      x ≡ c' + d' →
      P c ≡ c →
      P c' ≡ c' →
      P d ≡ 0# →
      P d' ≡ 0# →
      (c ≡ c') × (d ≡ d')

------------------------------------------------------------------------
-- Non-expansive idempotent projection axioms
------------------------------------------------------------------------

record NonExpansiveProjection {C : TestContext} (P : TestContext.S C → TestContext.S C) : Set₁ where
  open TestContext C renaming (S to S₀; _S+_ to _+_; _S-_ to _-_; 0# to 0#; dist to dist₀)
  field
    idem  : ∀ x → P (P x) ≡ P x
    nonexp : ∀ x y → dist₀ (P x) (P y) ≡ dist₀ x y
    -- (If you want ≤ instead of ≡, change dist codomain to ℚ/ℝ and use ≤.)

------------------------------------------------------------------------
-- Orthogonality: “no double counting” in the induced quadratic energy
--
-- This is the *test* you want Agda to force:
--   from RecognisableLift + NonExpansiveProjection (+ stability axiom),
--   derive Pythagorean split for a quadratic norm and orthogonality.
------------------------------------------------------------------------

record OrthogonalSplit {C : TestContext} (P : TestContext.S C → TestContext.S C) : Set₁ where
  open TestContext C renaming (S to S₀; _S+_ to _+_; _S-_ to _-_; 0# to 0#; ∥_∥ to ∥_∥₀)
  field
    ⟂-pred : S₀ → S₀ → Set          -- “orthogonal” predicate (abstract)
    pythag :
      ∀ x →
      let c = P x
          d = x - P x
      in  ∥_∥₀ x ≡ (∥_∥₀ c) × (∥_∥₀ d)   -- placeholder shape; replace with numeric identity
    orth :
      ∀ x →
      let c = P x
          d = x - P x
      in  ⟂-pred c d

------------------------------------------------------------------------
-- The Master Theorem (as a test harness)
------------------------------------------------------------------------

record ProjectionContractionOrthogonalityAxioms (C : TestContext) : Set₁ where
  field
    -- Stability premise: the multiscale hierarchy must forbid leakage.
    StabilityNoLeakage :
      (P : TestContext.S C → TestContext.S C) → Set

    MasterTheorem :
      (P : TestContext.S C → TestContext.S C) →
      RecognisableLift {C = C} P →
      NonExpansiveProjection {C = C} P →
      StabilityNoLeakage P →
      OrthogonalSplit {C = C} P
