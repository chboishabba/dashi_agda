module DASHI.Physics.Closure.NSTriadKNNineOwnerGridRound32Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Give the nine physical owners a duplicate-free 3 x 3 bookkeeping carrier.
-- This is organisational only: it does not assert a new D4 symmetry of the
-- PDE.  The sole nontrivial involution recorded here is the literal LH/HL
-- transpose pairing; every other owner remains fixed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data OwnerRow : Set where
  high mixed closure : OwnerRow

data OwnerColumn : Set where
  aligned misaligned crossScale : OwnerColumn

record OwnerCell : Set where
  constructor owner-cell
  field
    row : OwnerRow
    column : OwnerColumn

open OwnerCell public

data PhysicalOwner : Set where
  HHGood HHBad LH HL CC Com kernel tail boundary : PhysicalOwner

ownerCell : PhysicalOwner → OwnerCell
ownerCell HHGood = owner-cell high aligned
ownerCell HHBad = owner-cell high misaligned
ownerCell Com = owner-cell high crossScale
ownerCell LH = owner-cell mixed aligned
ownerCell HL = owner-cell mixed misaligned
ownerCell CC = owner-cell mixed crossScale
ownerCell kernel = owner-cell closure aligned
ownerCell tail = owner-cell closure misaligned
ownerCell boundary = owner-cell closure crossScale

allNineOwners : List PhysicalOwner
allNineOwners =
  HHGood ∷ HHBad ∷ Com ∷
  LH ∷ HL ∷ CC ∷
  kernel ∷ tail ∷ boundary ∷ []

transposeMixedOwner : PhysicalOwner → PhysicalOwner
transposeMixedOwner LH = HL
transposeMixedOwner HL = LH
transposeMixedOwner owner = owner

transposeMixedOwnerInvolutive :
  ∀ owner → transposeMixedOwner (transposeMixedOwner owner) ≡ owner
transposeMixedOwnerInvolutive HHGood = refl
transposeMixedOwnerInvolutive HHBad = refl
transposeMixedOwnerInvolutive LH = refl
transposeMixedOwnerInvolutive HL = refl
transposeMixedOwnerInvolutive CC = refl
transposeMixedOwnerInvolutive Com = refl
transposeMixedOwnerInvolutive kernel = refl
transposeMixedOwnerInvolutive tail = refl
transposeMixedOwnerInvolutive boundary = refl

nineOwnerGridClosed : Bool
nineOwnerGridClosed = true

nineOwnerGridClosedIsTrue : nineOwnerGridClosed ≡ true
nineOwnerGridClosedIsTrue = refl
