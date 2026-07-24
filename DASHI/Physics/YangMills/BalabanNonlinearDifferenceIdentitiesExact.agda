module DASHI.Physics.YangMills.BalabanNonlinearDifferenceIdentitiesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact

------------------------------------------------------------------------
-- Exact algebra used repeatedly by the five Hessian and seven nonlinear
-- estimates.  The analytic norm bounds remain separate, but no producer needs
-- to re-assume these product-difference expansions.
------------------------------------------------------------------------

bilinearDifferenceIdentity : ∀ a b c d →
  a * b - c * d
  ≡ a * (b - d) + (a - c) * d
bilinearDifferenceIdentity = ℚRing.solve-∀

bilinearDifferenceIdentityRight : ∀ a b c d →
  a * b - c * d
  ≡ (a - c) * b + c * (b - d)
bilinearDifferenceIdentityRight = ℚRing.solve-∀

trilinearDifferenceIdentity : ∀ a b c d e f →
  (a * b) * c - (d * e) * f
  ≡ (a * b) * (c - f)
    + (a * (b - e)) * f
    + ((a - d) * e) * f
trilinearDifferenceIdentity = ℚRing.solve-∀

squareDifferenceIdentity : ∀ a b →
  sq a - sq b ≡ (a - b) * (a + b)
squareDifferenceIdentity = ℚRing.solve-∀

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

quadraticPerturbationIdentity : ∀ base perturbation →
  sq (base + perturbation) - sq base
  ≡ twoℚ * (base * perturbation) + sq perturbation
quadraticPerturbationIdentity = ℚRing.solve-∀

adjointPenaltyDifferenceIdentity : ∀ base adjointDifference →
  sq (base + adjointDifference) - sq base
  ≡ twoℚ * (base * adjointDifference) + sq adjointDifference
adjointPenaltyDifferenceIdentity = quadraticPerturbationIdentity

blockPenaltyDifferenceIdentity : ∀ base blockDifference →
  sq (base + blockDifference) - sq base
  ≡ twoℚ * (base * blockDifference) + sq blockDifference
blockPenaltyDifferenceIdentity = quadraticPerturbationIdentity

------------------------------------------------------------------------
-- Canonical totals of the five and seven selected majorants.
------------------------------------------------------------------------

fiveComponentCanonical : QuadraticMajorant
fiveComponentCanonical = quadraticMajorant 136 228

sevenComponentCanonical : QuadraticMajorant
sevenComponentCanonical = quadraticMajorant 21 15

fiveComponentCanonicalExact :
  fiveComponentCandidate ≡ fiveComponentCanonical
fiveComponentCanonicalExact = refl

sevenComponentCanonicalExact :
  sevenComponentCandidate ≡ sevenComponentCanonical
sevenComponentCanonicalExact = refl

fiveComponentDyadicNumeratorExact : ∀ exponent →
  evaluateDyadicNumerator fiveComponentCandidate exponent
  ≡ 136 * pow2 exponent + 228
fiveComponentDyadicNumeratorExact exponent = refl

sevenComponentDyadicNumeratorExact : ∀ exponent →
  evaluateDyadicNumerator sevenComponentCandidate exponent
  ≡ 21 * pow2 exponent + 15
sevenComponentDyadicNumeratorExact exponent = refl

bilinearDifferenceAlgebraLevel : ProofLevel
bilinearDifferenceAlgebraLevel = computed

trilinearDifferenceAlgebraLevel : ProofLevel
trilinearDifferenceAlgebraLevel = computed

fiveAndSevenCanonicalCoefficientLevel : ProofLevel
fiveAndSevenCanonicalCoefficientLevel = computed

physicalFiveOperatorNormBoundsLevel : ProofLevel
physicalFiveOperatorNormBoundsLevel = conditional

physicalSevenNonlinearNormBoundsLevel : ProofLevel
physicalSevenNonlinearNormBoundsLevel = conditional
