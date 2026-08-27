module DASHI.Biology.TernaryRotationReflectionSeparationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Finite dihedral relation returned from Aristotle:
--   Lean/Spine/TritCarrier.lean
--
-- Rotation and polarity reflection are different operators.  They satisfy the
-- finite D3 conjugacy relation reflection * rotation = rotation^2 * reflection.

rotateTrit : Triadic.KernelTrit → Triadic.KernelTrit
rotateTrit Triadic.negativeTrit = Triadic.zeroTrit
rotateTrit Triadic.zeroTrit = Triadic.positiveTrit
rotateTrit Triadic.positiveTrit = Triadic.negativeTrit

rotateTritCube :
  (t : Triadic.KernelTrit) →
  rotateTrit (rotateTrit (rotateTrit t)) ≡ t
rotateTritCube Triadic.negativeTrit = refl
rotateTritCube Triadic.zeroTrit = refl
rotateTritCube Triadic.positiveTrit = refl

reflectTrit : Triadic.KernelTrit → Triadic.KernelTrit
reflectTrit = Triadic.negateTrit

reflectTritSquare :
  (t : Triadic.KernelTrit) → reflectTrit (reflectTrit t) ≡ t
reflectTritSquare = Triadic.negateTritInvolutive

rotateTwice : Triadic.KernelTrit → Triadic.KernelTrit
rotateTwice t = rotateTrit (rotateTrit t)

dihedralConjugacy :
  (t : Triadic.KernelTrit) →
  reflectTrit (rotateTrit t)
  ≡
  rotateTwice (reflectTrit t)
dihedralConjugacy Triadic.negativeTrit = refl
dihedralConjugacy Triadic.zeroTrit = refl
dihedralConjugacy Triadic.positiveTrit = refl

rotationMovesNeutral :
  rotateTrit Triadic.zeroTrit ≡ Triadic.positiveTrit
rotationMovesNeutral = refl

reflectionFixesNeutral :
  reflectTrit Triadic.zeroTrit ≡ Triadic.zeroTrit
reflectionFixesNeutral = refl

rotationAndReflectionDifferAtNeutral :
  rotateTrit Triadic.zeroTrit ≡ reflectTrit Triadic.zeroTrit → ⊥
rotationAndReflectionDifferAtNeutral ()

record TernaryOperatorBoundary : Set where
  constructor ternaryOperatorBoundary
  field
    cyclicAdvanceEqualsPolarityReflection : Bool
    cyclicAdvanceEqualsPolarityReflectionIsFalse :
      cyclicAdvanceEqualsPolarityReflection ≡ false

    movingLineChangeCanBeCollapsedToOneGenericOperator : Bool
    movingLineChangeCanBeCollapsedToOneGenericOperatorIsFalse :
      movingLineChangeCanBeCollapsedToOneGenericOperator ≡ false

canonicalTernaryOperatorBoundary : TernaryOperatorBoundary
canonicalTernaryOperatorBoundary =
  ternaryOperatorBoundary false refl false refl
