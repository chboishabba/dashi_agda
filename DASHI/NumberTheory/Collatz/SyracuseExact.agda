module DASHI.NumberTheory.Collatz.SyracuseExact where

------------------------------------------------------------------------
-- LITERAL SHORTCUT SYRACUSE DYNAMICS
--
-- The fine dynamical object is a positive integer.  We represent n > 0 by
-- its predecessor index, so positivity is structural rather than a Boolean
-- assertion.  No probability, residue class, or finite affine chain enters
-- this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
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
-- Shortcut Collatz/Syracuse map.
--
-- Positive input x is represented by n=x-1.  The result is again stored by
-- predecessor.  Modulo two has only remainders zero/one; pattern matching on
-- zero versus successor therefore selects the even/odd branch without adding
-- a second dynamical object.
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

------------------------------------------------------------------------
-- Promotion boundary.
--
-- General even/odd arithmetic rewriting of toNat(shortcutSyracuse x) is kept
-- separate from the definition.  Downstream same-object work consumes the
-- literal executable map above; it may not replace it by the finite 3z/3z-1
-- chain merely because both expose binary branches.
------------------------------------------------------------------------

record SyracuseLiteralBoundary : Set where
  constructor syracuseLiteralBoundary
  field
    positiveCarrierStructural : Nat
    probabilityIntroducedHere : Nat
    finiteAffineChainIdentifiedWithSyracuse : Nat

canonicalSyracuseLiteralBoundary : SyracuseLiteralBoundary
canonicalSyracuseLiteralBoundary = syracuseLiteralBoundary 1 0 0
