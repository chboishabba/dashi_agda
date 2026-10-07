module DASHI.Moonshine.OggSSPTriadicKernelCanonicalFieldActionFrontierExact where

------------------------------------------------------------------------
-- CANONICAL FIELD-ACTION FRONTIER FOR THE TRIADIC KERNELS
--
-- The canonical TriadicPAdicCodec owner supplies the carrier, lift and global
-- inversion.  The max-cut tranche adds the full coordinate F3 vector-space
-- laws and verifies chosen GF(3^d) multiplications at runtime.  What remains
-- for intrinsic finite-field recognition is an independently sourced
-- multiplication/Frobenius action on the same existing carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact as Linear
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated

record CanonicalFieldActionSocket (d : Nat) : Set₁ where
  field
    one : Codec.Kernel d
    multiply : Codec.Kernel d → Codec.Kernel d → Codec.Kernel d
    frobenius : Codec.Kernel d → Codec.Kernel d

    -- The independently sourced multiplication must extend the already-paid
    -- F3 scalar action rather than replacing it with an unrelated operation.
    minusOneActsAsExistingInversion :
      (x : Codec.Kernel d) →
      multiply (Linear.scaleKernel Trit.neg one) x ≡ Codec.invertKernel x

    -- Frobenius must be a homomorphism for the same multiplication.
    frobeniusPreservesMultiply :
      (x y : Codec.Kernel d) →
      frobenius (multiply x y) ≡ multiply (frobenius x) (frobenius y)

    -- Characteristic-three compatibility on the already-owned additive
    -- surface.  This keeps the new action on the same physical/formal object.
    frobeniusPreservesAdd :
      (x y : Codec.Kernel d) →
      frobenius (Linear.addKernel x y)
      ≡ Linear.addKernel (frobenius x) (frobenius y)

-- Concrete target depths.  No canonical inhabitant is invented here.
K4CanonicalFieldAction : Set₁
K4CanonicalFieldAction = CanonicalFieldActionSocket 4

K5CanonicalFieldAction : Set₁
K5CanonicalFieldAction = CanonicalFieldActionSocket 5

K6CanonicalFieldAction : Set₁
K6CanonicalFieldAction = CanonicalFieldActionSocket 6

record CanonicalFieldActionFrontierBoundary : Set where
  constructor canonical-field-action-frontier-boundary
  field
    coordinateF3VectorSpacePaid : Bool
    chosenExtensionFieldRuntimePaid : Bool
    existingInversionMinusOneWeldPaid : Bool
    chosenK4GF9SubfieldMapPaid : Bool
    canonicalMultiplicationFromPriorCodecPaid : Bool
    canonicalFrobeniusFromPriorCodecPaid : Bool
    fullFieldActionRecognitionPaid : Bool

canonicalFieldActionFrontierBoundary : CanonicalFieldActionFrontierBoundary
canonicalFieldActionFrontierBoundary =
  canonical-field-action-frontier-boundary
    true
    Generated.chosenFieldMultiplicationRuntimeVerified
    true
    Generated.k4T5ChosenSubfieldObjectMapPaid
    false false false
