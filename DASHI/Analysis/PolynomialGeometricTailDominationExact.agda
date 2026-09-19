module DASHI.Analysis.PolynomialGeometricTailDominationExact where

------------------------------------------------------------------------
-- APPLICATION-NEUTRAL DOMINATED FINITE TAILS
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- This owner extracts the mathematical core shared by the Step-V
-- polynomial/geometric lane and the summable-increment/Casimir Cauchy lanes:
--
--   pointwise term domination
--        +
--   monotone finite addition
--        ->
--   domination of every finite tail.
--
-- A consumer may then supply its own notion of "small at precision p".
-- If that notion is downward closed under <=, eventual uniform smallness of
-- the geometric majorant tail transfers automatically to the dominated tail.
--
-- In the Eisenstein application:
--
--   term(n)     = n^k r^n
--   majorant(n) = M (r')^n
--
-- after the existing direct-ratio / finite-prefix domination step.  This file
-- deliberately does NOT assert that such a domination exists on an arbitrary
-- scalar carrier, nor does it manufacture the backend's IsCauchy predicate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

record OrderedTailKernel (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value

    addMonotone :
      ∀ {left₁ left₂ right₁ right₂} →
      LessEqual left₁ left₂ →
      LessEqual right₁ right₂ →
      LessEqual (add left₁ right₁) (add left₂ right₂)

open OrderedTailKernel public

finiteTail :
  ∀ {Scalar : Set} →
  (K : OrderedTailKernel Scalar) →
  (Nat → Scalar) →
  Nat →
  Nat →
  Scalar
finiteTail K term start zero = zero K
finiteTail K term start (suc count) =
  add K
    (term start)
    (finiteTail K term (suc start) count)

finiteTailDomination :
  ∀ {Scalar : Set}
    (K : OrderedTailKernel Scalar)
    (term majorant : Nat → Scalar) →
  (∀ index → LessEqual K (term index) (majorant index)) →
  ∀ start count →
  LessEqual K
    (finiteTail K term start count)
    (finiteTail K majorant start count)
finiteTailDomination K term majorant pointwise start zero =
  reflexive K (zero K)
finiteTailDomination K term majorant pointwise start (suc count) =
  addMonotone K
    (pointwise start)
    (finiteTailDomination
      K term majorant pointwise (suc start) count)

------------------------------------------------------------------------
-- Generic vanishing semantics.
--
-- Precision is indexed by Nat so this owner does not invent an epsilon/norm
-- structure for consumers that already have one.
------------------------------------------------------------------------

record TailSmallness
    {Scalar : Set}
    (K : OrderedTailKernel Scalar) : Set₁ where
  field
    SmallAt : Nat → Scalar → Set

    downwardClosed :
      ∀ {precision lower upper} →
      LessEqual K lower upper →
      SmallAt precision upper →
      SmallAt precision lower

open TailSmallness public

TailVanishes :
  ∀ {Scalar : Set}
    (K : OrderedTailKernel Scalar) →
    TailSmallness K →
    (Nat → Scalar) →
    Set
TailVanishes K S term =
  ∀ precision →
  Σ Nat (λ start →
    ∀ count →
    SmallAt S precision (finiteTail K term start count))

dominatedTailVanishes :
  ∀ {Scalar : Set}
    (K : OrderedTailKernel Scalar)
    (term majorant : Nat → Scalar)
    (S : TailSmallness K) →
  (∀ index → LessEqual K (term index) (majorant index)) →
  TailVanishes K S majorant →
  TailVanishes K S term
dominatedTailVanishes K term majorant S pointwise majorantVanishes precision
  with majorantVanishes precision
... | start , majorantSmall =
  start ,
  λ count →
    downwardClosed S
      (finiteTailDomination
        K term majorant pointwise start count)
      (majorantSmall count)
