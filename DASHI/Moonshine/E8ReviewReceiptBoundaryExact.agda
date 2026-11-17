{-# OPTIONS --safe #-}
module DASHI.Moonshine.E8ReviewReceiptBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- A review receipt records scope, not an E8 lattice isometry or
-- a Monster VOA representation theorem.
record E8ReviewReceipt : Set where
  constructor e8ReviewReceipt
  field
    sourceOwner : String
    reviewScope : String
    kernelChecked : Bool
    sameObjectMonsterPromoted : Bool

currentE8Review : E8ReviewReceipt
currentE8Review = e8ReviewReceipt
  "DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact"
  "ternary-27 C3 spectral bridge, not E8/Monster same-object"
  false false

reviewNotKernelChecked :
  E8ReviewReceipt.kernelChecked currentE8Review ≡ false
reviewNotKernelChecked = refl

reviewDoesNotPromoteMonster :
  E8ReviewReceipt.sameObjectMonsterPromoted currentE8Review ≡ false
reviewDoesNotPromoteMonster = refl
