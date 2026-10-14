module DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact where

------------------------------------------------------------------------
-- VIRTUAL IMMUTABLE BASE + SPARSE WRITE RESIDUAL
--
-- A virtual input must survive candidate writes without reconstructing the
-- complete base string.  The correct representation is therefore:
--
--   immutable virtual base read
--        + latest-write sparse residual
--        -> exact current cell read.
--
-- This owner is generic in the cell alphabet.  It deliberately does not know
-- about Cook formulae, Turing machines or SAT.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Tiny decidable natural equality used by the finite residual map.
------------------------------------------------------------------------

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc right) = false
natEqual (suc left) zero = false
natEqual (suc left) (suc right) = natEqual left right

natEqualRefl : (n : Nat) → natEqual n n ≡ true
natEqualRefl zero = refl
natEqualRefl (suc n) = natEqualRefl n

natEqualSound : ∀ {left right} → natEqual left right ≡ true → left ≡ right
natEqualSound {zero} {zero} proof = refl
natEqualSound {zero} {suc right} ()
natEqualSound {suc left} {zero} ()
natEqualSound {suc left} {suc right} proof
  with natEqualSound {left} {right} proof
... | refl = refl

natEqualFalseFromApart :
  ∀ {left right} →
  (left ≡ right → ⊥) →
  natEqual left right ≡ false
natEqualFalseFromApart {zero} {zero} apart
  with apart refl
... | ()
natEqualFalseFromApart {zero} {suc right} apart = refl
natEqualFalseFromApart {suc left} {zero} apart = refl
natEqualFalseFromApart {suc left} {suc right} apart
  with natEqual left right
... | false = refl
... | true
  with natEqualSound {left} {right} refl
... | refl
  with apart refl
... | ()

------------------------------------------------------------------------
-- Latest-write map.  New writes are consed at the front, so lookup is O(depth)
-- and has no hidden global rebuilding step.
------------------------------------------------------------------------

record WriteEntry (Cell : Set) : Set where
  constructor write-entry
  field
    address : Nat
    value : Cell

open WriteEntry public

WriteResidual : Set → Set
WriteResidual Cell = List (WriteEntry Cell)

latestWrite :
  ∀ {Cell : Set} →
  Nat → WriteResidual Cell → Maybe Cell
latestWrite requested [] = nothing
latestWrite requested (entry ∷ rest)
  with natEqual requested (address entry)
... | true = just (value entry)
... | false = latestWrite requested rest

writeResidual :
  ∀ {Cell : Set} →
  Nat → Cell → WriteResidual Cell → WriteResidual Cell
writeResidual requested cell residual =
  write-entry requested cell ∷ residual

latestWriteSame :
  ∀ {Cell : Set}
    (requested : Nat)
    (cell : Cell)
    (residual : WriteResidual Cell) →
  latestWrite requested (writeResidual requested cell residual)
  ≡ just cell
latestWriteSame requested cell residual
  rewrite natEqualRefl requested = refl

latestWriteDifferent :
  ∀ {Cell : Set}
    {read write : Nat}
    (apart : read ≡ write → ⊥)
    (cell : Cell)
    (residual : WriteResidual Cell) →
  latestWrite read (writeResidual write cell residual)
  ≡ latestWrite read residual
latestWriteDifferent {read = read} {write = write} apart cell residual
  rewrite natEqualFalseFromApart apart = refl

------------------------------------------------------------------------
-- Immutable virtual base and exact overlay read.
------------------------------------------------------------------------

record VirtualTapeBase (Cell : Set) : Set₁ where
  field
    baseRead : Nat → Maybe Cell

open VirtualTapeBase public

overlayRead :
  ∀ {Cell : Set} →
  VirtualTapeBase Cell →
  WriteResidual Cell →
  Nat → Maybe Cell
overlayRead base residual requested
  with latestWrite requested residual
... | just cell = just cell
... | nothing = baseRead base requested

overlayReadWritten :
  ∀ {Cell : Set}
    (base : VirtualTapeBase Cell)
    (residual : WriteResidual Cell)
    (requested : Nat)
    (cell : Cell) →
  overlayRead base (writeResidual requested cell residual) requested
  ≡ just cell
overlayReadWritten base residual requested cell
  rewrite latestWriteSame requested cell residual = refl

overlayReadUnwritten :
  ∀ {Cell : Set}
    (base : VirtualTapeBase Cell)
    (residual : WriteResidual Cell)
    (requested : Nat) →
  latestWrite requested residual ≡ nothing →
  overlayRead base residual requested ≡ baseRead base requested
overlayReadUnwritten base residual requested proof
  rewrite proof = refl

overlayReadOtherWrite :
  ∀ {Cell : Set}
    (base : VirtualTapeBase Cell)
    {read write : Nat}
    (apart : read ≡ write → ⊥)
    (cell : Cell)
    (residual : WriteResidual Cell) →
  overlayRead base (writeResidual write cell residual) read
  ≡ overlayRead base residual read
overlayReadOtherWrite base {read} {write} apart cell residual
  rewrite latestWriteDifferent apart cell residual = refl

------------------------------------------------------------------------
-- Consumer-relative exactness boundary.
--
-- Untouched reads factor through the immutable base.  Touched reads factor
-- through the sparse residual.  Exact current-tape access therefore does not
-- require reconstructing or copying the entire base representation.
------------------------------------------------------------------------
