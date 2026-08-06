module DASHI.Physics.Foundations.FiniteWeightedTernaryKernelExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Finite analogue of symmetry-compatible weighted aggregation.  Coordinate
-- exchange represents one geometric symmetry of a two-coordinate sheet.

swapCoordinates : Triadic.NineSheet → Triadic.NineSheet
swapCoordinates (a , b) = b , a

symmetricKernel : Triadic.NineSheet → Triadic.NineSheet
symmetricKernel (a , b) = b , a

symmetricKernelCommutesWithCoordinateSwap :
  (sheet : Triadic.NineSheet) →
  symmetricKernel (swapCoordinates sheet)
  ≡
  swapCoordinates (symmetricKernel sheet)
symmetricKernelCommutesWithCoordinateSwap (a , b) = refl

symmetricKernelCommutesWithInvolution :
  (sheet : Triadic.NineSheet) →
  symmetricKernel (Triadic.negateNine sheet)
  ≡
  Triadic.negateNine (symmetricKernel sheet)
symmetricKernelCommutesWithInvolution (a , b) = refl

------------------------------------------------------------------------
-- An asymmetric coupling keeps only the first coordinate.  The explicit
-- witness shows spatial equivariance does not follow for arbitrary weights.

asymmetricKernel : Triadic.NineSheet → Triadic.NineSheet
asymmetricKernel (a , b) = a , a

asymmetricWitness : Triadic.NineSheet
asymmetricWitness = Triadic.negativeTrit , Triadic.positiveTrit

asymmetricKernelBreaksCoordinateSwap :
  asymmetricKernel (swapCoordinates asymmetricWitness)
  ≡
  swapCoordinates (asymmetricKernel asymmetricWitness)
  →
  ⊥
asymmetricKernelBreaksCoordinateSwap ()

------------------------------------------------------------------------
-- A nonzero fixed bias can break involution equivariance.  This finite map is
-- a table-level witness for the role of an unpaired bias term.

biasedUpdate : Triadic.KernelTrit → Triadic.KernelTrit
biasedUpdate Triadic.negativeTrit = Triadic.zeroTrit
biasedUpdate Triadic.zeroTrit = Triadic.positiveTrit
biasedUpdate Triadic.positiveTrit = Triadic.positiveTrit

biasBreaksInvolutionAtZero :
  biasedUpdate (Triadic.negateTrit Triadic.zeroTrit)
  ≡
  Triadic.negateTrit (biasedUpdate Triadic.zeroTrit)
  →
  ⊥
biasBreaksInvolutionAtZero ()

------------------------------------------------------------------------
-- Linear aggregation and ternary quantisation are represented as separate
-- finite stages rather than calling their composition a linear projection.

data Preactivation : Set where
  negativePreactivation : Preactivation
  zeroPreactivation : Preactivation
  positivePreactivation : Preactivation

quantiseTernary : Preactivation → Triadic.KernelTrit
quantiseTernary negativePreactivation = Triadic.negativeTrit
quantiseTernary zeroPreactivation = Triadic.zeroTrit
quantiseTernary positivePreactivation = Triadic.positiveTrit

quantisationPreservesZero :
  quantiseTernary zeroPreactivation ≡ Triadic.zeroTrit
quantisationPreservesZero = refl

record FiniteWeightedTernaryKernelBoundary : Set where
  constructor finiteWeightedTernaryKernelBoundary
  field
    arbitraryWeightsGuaranteeGeometricEquivariance : Bool
    arbitraryWeightsGuaranteeGeometricEquivarianceIsFalse :
      arbitraryWeightsGuaranteeGeometricEquivariance ≡ false

    unpairedBiasPreservesSignInvolution : Bool
    unpairedBiasPreservesSignInvolutionIsFalse :
      unpairedBiasPreservesSignInvolution ≡ false

    ternaryQuantisationIsLinearProjection : Bool
    ternaryQuantisationIsLinearProjectionIsFalse :
      ternaryQuantisationIsLinearProjection ≡ false

open FiniteWeightedTernaryKernelBoundary public

canonicalFiniteWeightedTernaryKernelBoundary :
  FiniteWeightedTernaryKernelBoundary
canonicalFiniteWeightedTernaryKernelBoundary =
  finiteWeightedTernaryKernelBoundary false refl false refl false refl
