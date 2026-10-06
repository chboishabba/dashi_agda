module DASHI.NumberTheory.Collatz.SyracuseExact where

------------------------------------------------------------------------
-- LITERAL SHORTCUT SYRACUSE DYNAMICS
--
-- The fine dynamical object is a positive integer.  We represent n > 0 by
-- its predecessor index, so positivity is structural rather than a Boolean
-- assertion.  No probability, residue class, or finite affine chain enters
-- this module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_)
open import Data.Nat.DivMod using (_/_; _%_)

record PositiveNat : Set where
  constructor positiveNat
  field
    predecessor : Nat

open PositiveNat public

toNat : PositiveNat → Nat
toNat (positiveNat n) = suc n

------------------------------------------------------------------------
-- Literal parity observable.  Keeping it here makes the branch selector and
-- the itinerary consume the same definition rather than two extensionally
-- equal tests that would later need a weld.
------------------------------------------------------------------------

parityBool : PositiveNat → Bool
parityBool (positiveNat n) with (suc n) % 2
... | zero = false
... | suc _ = true

------------------------------------------------------------------------
-- Shortcut Collatz/Syracuse map.
------------------------------------------------------------------------

shortcutIndex : Nat → Nat
shortcutIndex n with (suc n) % 2
... | zero = ((suc n) / 2) ∸ 1
... | suc _ = (((3 * suc n) + 1) / 2) ∸ 1

shortcutSyracuse : PositiveNat → PositiveNat
shortcutSyracuse (positiveNat n) = positiveNat (shortcutIndex n)

-- Positivity is paid by construction: the codomain itself is PositiveNat.
shortcutSyracusePositive : PositiveNat → PositiveNat
shortcutSyracusePositive = shortcutSyracuse

------------------------------------------------------------------------
-- Exact branch equations on the structural positive representation.
--
-- These are theorem-bearing general equations, not finite specimens.  They
-- are definitionally aligned with `parityBool` because both inspect the same
-- modulo-two remainder.
------------------------------------------------------------------------

shortcutIndexParityFalse :
  (n : Nat) →
  parityBool (positiveNat n) ≡ false →
  shortcutIndex n ≡ ((suc n) / 2) ∸ 1
shortcutIndexParityFalse n with (suc n) % 2
... | zero = λ _ → refl
... | suc _ = λ ()

shortcutIndexParityTrue :
  (n : Nat) →
  parityBool (positiveNat n) ≡ true →
  shortcutIndex n ≡ (((3 * suc n) + 1) / 2) ∸ 1
shortcutIndexParityTrue n with (suc n) % 2
... | zero = λ ()
... | suc _ = λ _ → refl

shortcutSyracuseParityFalse :
  (n : Nat) →
  parityBool (positiveNat n) ≡ false →
  shortcutSyracuse (positiveNat n)
  ≡ positiveNat (((suc n) / 2) ∸ 1)
shortcutSyracuseParityFalse n even =
  cong positiveNat (shortcutIndexParityFalse n even)

shortcutSyracuseParityTrue :
  (n : Nat) →
  parityBool (positiveNat n) ≡ true →
  shortcutSyracuse (positiveNat n)
  ≡ positiveNat ((((3 * suc n) + 1) / 2) ∸ 1)
shortcutSyracuseParityTrue n odd =
  cong positiveNat (shortcutIndexParityTrue n odd)

syracuseIterate : Nat → PositiveNat → PositiveNat
syracuseIterate zero x = x
syracuseIterate (suc k) x = syracuseIterate k (shortcutSyracuse x)

syracuseIterateSuc :
  (k : Nat) → (x : PositiveNat) →
  syracuseIterate (suc k) x ≡ syracuseIterate k (shortcutSyracuse x)
syracuseIterateSuc k x = refl

------------------------------------------------------------------------
-- Executable branch specimens.  These pin the literal orientation used by
-- every downstream parity/cylinder theorem.
------------------------------------------------------------------------

one two three four five six seven eight : PositiveNat
one   = positiveNat 0
two   = positiveNat 1
three = positiveNat 2
four  = positiveNat 3
five  = positiveNat 4
six   = positiveNat 5
seven = positiveNat 6
eight = positiveNat 7

shortcut-one : shortcutSyracuse one ≡ two
shortcut-one = refl

shortcut-two : shortcutSyracuse two ≡ one
shortcut-two = refl

shortcut-three : shortcutSyracuse three ≡ five
shortcut-three = refl

shortcut-four : shortcutSyracuse four ≡ two
shortcut-four = refl

shortcut-five : shortcutSyracuse five ≡ eight
shortcut-five = refl

shortcut-six : shortcutSyracuse six ≡ three
shortcut-six = refl

shortcut-seven : shortcutSyracuse seven ≡ positiveNat 10
shortcut-seven = refl

shortcut-eight : shortcutSyracuse eight ≡ four
shortcut-eight = refl

record SyracuseLiteralBoundary : Set where
  constructor syracuseLiteralBoundary
  field
    positiveCarrierStructural : Nat
    generalParityBranchEquationsOwned : Nat
    probabilityIntroducedHere : Nat
    finiteAffineChainIdentifiedWithSyracuse : Nat

canonicalSyracuseLiteralBoundary : SyracuseLiteralBoundary
canonicalSyracuseLiteralBoundary = syracuseLiteralBoundary 1 1 0 0
