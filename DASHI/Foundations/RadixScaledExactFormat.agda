module DASHI.Foundations.RadixScaledExactFormat where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.BinaryFloatingPoint as Binary

------------------------------------------------------------------------
-- Generic structural owner extracted from the existing binary floating-point
-- representation.  Radix, scale policy and coordinate role remain distinct.

data ExactRadix : Set where
  radix2 : ExactRadix
  radix3 : ExactRadix
  radix10 : ExactRadix

binaryRadixEmbedding : Binary.Radix → ExactRadix
binaryRadixEmbedding Binary.binaryRadix = radix2
binaryRadixEmbedding Binary.decimalRadix = radix10

record ScaledExactFormat : Set where
  constructor scaledExactFormat
  field
    radix : ExactRadix
    orientationRole : Binary.CoordinateRole
    scaleRole : Binary.CoordinateRole
    refinementRole : Binary.CoordinateRole
open ScaledExactFormat public

bf16ScaledExactFormat : ScaledExactFormat
bf16ScaledExactFormat =
  scaledExactFormat
    radix2
    Binary.orientationRole
    Binary.scaleTransportRole
    Binary.localRefinementRole

record WidthAllocation : Set where
  constructor widthAllocation
  field
    explicitScaleWidth : Nat
    refinementWidth : Nat
open WidthAllocation public

bf16WidthAllocation : WidthAllocation
bf16WidthAllocation = widthAllocation 8 7

record TaperedWidthAllocation (Parameter : Set) : Set₁ where
  constructor taperedWidthAllocation
  field
    totalPayloadWidth : Nat
    scaleWidth : Parameter → Nat
    refinementWidth : Parameter → Nat
    conserved :
      (p : Parameter) →
      scaleWidth p + refinementWidth p ≡ totalPayloadWidth
open TaperedWidthAllocation public

record RadixScaledBoundary : Set where
  constructor radixScaledBoundary
  field
    radixSeparatedFromScalePolicy : Bool
    orientationScaleRefinementRolesReused : Bool
    fixedAndTaperedAllocationsTypeDistinct : Bool

canonicalRadixScaledBoundary : RadixScaledBoundary
canonicalRadixScaledBoundary =
  radixScaledBoundary true true true
