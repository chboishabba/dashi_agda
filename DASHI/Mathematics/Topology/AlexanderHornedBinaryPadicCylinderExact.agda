module DASHI.Mathematics.Topology.AlexanderHornedBinaryPadicCylinderExact where

------------------------------------------------------------------------
-- EXACT BINARY CYLINDER INSTANCE FOR HATCHER HORN ADDRESSES.
--
-- EXISTING DONORS (original authorship preserved):
--   AlexanderHornedC3FiniteStageExact: Bit and sector-labelled horns;
--   DASHI.Codec.TriadicPAdicCodec: genuine CylinderSystem contract;
--   DASHI.Codec.TriadicPAdicCylinderExact: trit stream analogue;
--   DASHI.Geometry.SSP369Ultrametric: prefix/separation machinery.
--
-- CRITICAL RADIX DISCRIMINATOR:
-- Horn branching is BINARY (Cantor/Z_2), whereas the three
-- INDEPENDENT root sectors carry an external C3 action.
-- Trit cylinders and the ternary pair of pants are not the same
-- as the literal Hatcher binary horn subdivision.
--
-- This module inhabits the existing cylinder contract for infinite
-- chronological binary streams, proving every finite truncation
-- commutes with the previous depth. The old HornAddress.suffix is
-- newest-first because leftChild prepends; it is not silently
-- treated as a low-to-high 2-adic digit list.
--
-- Nothing here constructs a wild embedded ball, exterior pi1, a
-- metric on that exterior, or a p-adic field/analytic structure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Codec.TriadicPAdicCodec as Padic
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

BitStream : Set
BitStream = Nat → Horn.Bit

shiftStream : BitStream → BitStream
shiftStream stream n = stream (suc n)

data BitPrefix : Nat → Set where
  []ᵇ : BitPrefix zero
  _∷ᵇ_ : ∀ {n} → Horn.Bit → BitPrefix n → BitPrefix (suc n)

projectBits : (n : Nat) → BitStream → BitPrefix n
projectBits zero stream = []ᵇ
projectBits (suc n) stream =
  stream zero ∷ᵇ projectBits n (shiftStream stream)

dropNewest : (n : Nat) → BitPrefix (suc n) → BitPrefix n
dropNewest zero (b ∷ᵇ []ᵇ) = []ᵇ
dropNewest (suc n) (b ∷ᵇ bs) = b ∷ᵇ dropNewest n bs

binaryProjectionCompatible :
  (n : Nat) → (stream : BitStream) →
  dropNewest n (projectBits (suc n) stream) ≡ projectBits n stream
binaryProjectionCompatible zero stream = refl
binaryProjectionCompatible (suc n) stream
  rewrite binaryProjectionCompatible n (shiftStream stream) = refl

canonicalBinaryHornCylinder : Padic.CylinderSystem
canonicalBinaryHornCylinder = record
  { Padic.Residual = BitStream
  ; Padic.Cylinder = BitPrefix
  ; Padic.project = projectBits
  ; Padic.refine = dropNewest
  ; Padic.project-compatible = binaryProjectionCompatible
  }

-- Chronological interpretation of the old *newest-first* suffix.
-- One horn replacement prepends a young digit and therefore
-- appends the corresponding high-order 2-adic digit after reversal.
chronological : List Horn.Bit → List Horn.Bit
chronological [] = []
chronological (digit ∷ xs) =
  chronological xs ++ (digit ∷ [])

leftChildAddsHighOrderDigit : ∀ xs →
  chronological (Horn.left ∷ xs) ≡
    chronological xs ++ (Horn.left ∷ [])
leftChildAddsHighOrderDigit xs = refl

rightChildAddsHighOrderDigit : ∀ xs →
  chronological (Horn.right ∷ xs) ≡
    chronological xs ++ (Horn.right ∷ [])
rightChildAddsHighOrderDigit xs = refl

-- Keep the actual sector separate from the binary refinement.
record BinarySectorEnd : Set where
  constructor binary-sector-end
  field
    sector : C3.C3
    digits : BitStream

open BinarySectorEnd public

rotateEnd : BinarySectorEnd → BinarySectorEnd
rotateEnd (binary-sector-end c ds) =
  binary-sector-end (Horn.rotateSector c) ds

rotateEndCubedOnSector : ∀ x →
  sector (rotateEnd (rotateEnd (rotateEnd x))) ≡ sector x
rotateEndCubedOnSector (binary-sector-end c ds) =
  Horn.rotateSectorCubed c

rotateEndPreservesEveryBinaryCylinder :
  ∀ n x →
  projectBits n (digits (rotateEnd x)) ≡ projectBits n (digits x)
rotateEndPreservesEveryBinaryCylinder n x = refl

-- Equality of streams as a FUNCTION would require function
-- extensionality; the exact finite cylinder observations above
-- need no extensionality assumption.
