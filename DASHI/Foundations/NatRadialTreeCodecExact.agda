module DASHI.Foundations.NatRadialTreeCodecExact where

------------------------------------------------------------------------
-- NATURAL-NUMBER -> EXISTING RADIAL-TREE CODEC
--
-- This is arithmetic plumbing over `RadixValuationStageBridge`.  It does not
-- introduce a second radix tree.  At each outward refinement step the next
-- digit is the least-significant remainder modulo the positive radix and the
-- parent receives the corresponding natural-number quotient.
--
-- Consequently a depth-d address is the finite base-p residue presentation
-- needed by exact rational vertices such as m / p^d.  Analytic real-number
-- floor/fractional-part decisions are intentionally absent from this owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (_/_; m%n<n)

import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Foundations.RepresentationChartInvariant as Representation

------------------------------------------------------------------------
-- Positive-radix quotient and remainder digit.
------------------------------------------------------------------------

radixQuotient : Radix.RadixChart → Nat → Nat
radixQuotient
  (Radix.radix-chart (suc base) Representation.positive origin label)
  value =
  value / suc base

radixLastDigit :
  (chart : Radix.RadixChart) →
  Nat →
  Fin (Radix.radix chart)
radixLastDigit
  (Radix.radix-chart (suc base) Representation.positive origin label)
  value =
  fromℕ< (m%n<n value (suc base))

------------------------------------------------------------------------
-- Recursive finite address.
--
-- `RadialTreeAddress` appends outward digits.  Recursing first on the quotient
-- therefore records the ordinary base-p digits from the most significant of
-- the retained d places to the least significant place.
------------------------------------------------------------------------

natRadialAddress :
  (chart : Radix.RadixChart) →
  (depth : Nat) →
  Nat →
  Radix.RadialTreeAddress chart depth
natRadialAddress chart zero value = Radix.radial-root
natRadialAddress chart (suc depth) value =
  Radix.radial-extend
    (natRadialAddress chart depth (radixQuotient chart value))
    (radixLastDigit chart value)

natRadialAddressCoarsensToQuotient :
  (chart : Radix.RadixChart) →
  (depth value : Nat) →
  Radix.radialCoarsen (natRadialAddress chart (suc depth) value)
  ≡ natRadialAddress chart depth (radixQuotient chart value)
natRadialAddressCoarsensToQuotient chart depth value = refl

------------------------------------------------------------------------
-- Decode the retained finite address back to a natural number.
------------------------------------------------------------------------

radialValue :
  (chart : Radix.RadixChart) →
  ∀ {depth} →
  Radix.RadialTreeAddress chart depth →
  Nat
radialValue chart Radix.radial-root = zero
radialValue chart (Radix.radial-extend parent digit) =
  Radix.radix chart * radialValue chart parent + toℕ digit

radialValueAfterExtend :
  (chart : Radix.RadixChart) →
  ∀ {depth}
    (parent : Radix.RadialTreeAddress chart depth)
    (digit : Fin (Radix.radix chart)) →
  radialValue chart (Radix.radial-extend parent digit)
  ≡ Radix.radix chart * radialValue chart parent + toℕ digit
radialValueAfterExtend chart parent digit = refl

------------------------------------------------------------------------
-- Small exact regression fixtures.  These also pin the orientation of the
-- recursive quotient/remainder convention.
------------------------------------------------------------------------

binaryOneDigitThree :
  radialValue Radix.binaryChart
    (natRadialAddress Radix.binaryChart 1 3)
  ≡ 1
binaryOneDigitThree = refl

binaryThreeDigitsThirteen :
  radialValue Radix.binaryChart
    (natRadialAddress Radix.binaryChart 3 13)
  ≡ 5
binaryThreeDigitsThirteen = refl

ternaryTwoDigitsFourteen :
  radialValue Radix.ternaryChart
    (natRadialAddress Radix.ternaryChart 2 14)
  ≡ 5
ternaryTwoDigitsFourteen = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record NatRadialTreeCodecBoundary : Set where
  constructor nat-radial-tree-codec-boundary
  field
    existingRadialTreeReused : Bool
    positiveRadixEvidenceReused : Bool
    quotientRemainderDigitCompilerConstructed : Bool
    coarseningIsQuotientStep : Bool
    finiteAddressDecodingConstructed : Bool

    constructsAnalyticRealFloor : Bool
    identifiesRadixAddressWithPAdicCompletion : Bool
    provesAnyZetaOrMonsterClaim : Bool

open NatRadialTreeCodecBoundary public

canonicalNatRadialTreeCodecBoundary : NatRadialTreeCodecBoundary
canonicalNatRadialTreeCodecBoundary =
  nat-radial-tree-codec-boundary
    true true true true true
    false false false
