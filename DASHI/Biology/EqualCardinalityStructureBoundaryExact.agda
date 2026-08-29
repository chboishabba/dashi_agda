module DASHI.Biology.EqualCardinalityStructureBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryRotationReflectionSeparationExact as Ops

------------------------------------------------------------------------
-- Aristotle-return obstruction.
--
-- Lean/Spine/OggGrid.lean proves a concrete version for the fifteen Ogg primes:
-- equal cardinality does not provide an equivariant labelling when orbit
-- structure disagrees.  This module factors out the reusable finite theorem:
-- even on equal three-element carriers, a free order-three action cannot be
-- equivariantly identified with an action carrying a fixed point.

record EquivariantBijection : Set where
  constructor equivariantBijection
  field
    forward : Triadic.KernelTrit → Triadic.KernelTrit
    backward : Triadic.KernelTrit → Triadic.KernelTrit
    leftInverse :
      (x : Triadic.KernelTrit) → backward (forward x) ≡ x
    rightInverse :
      (y : Triadic.KernelTrit) → forward (backward y) ≡ y
    intertwines :
      (x : Triadic.KernelTrit) →
      forward (Ops.rotateTrit x)
      ≡
      Ops.reflectTrit (forward x)

open EquivariantBijection public

sourceRotationHasNoFixedPoint :
  (x : Triadic.KernelTrit) → Ops.rotateTrit x ≡ x → ⊥
sourceRotationHasNoFixedPoint Triadic.negativeTrit ()
sourceRotationHasNoFixedPoint Triadic.zeroTrit ()
sourceRotationHasNoFixedPoint Triadic.positiveTrit ()

fixedTargetPointForcesFixedSourcePoint :
  (e : EquivariantBijection) →
  Ops.rotateTrit (backward e Triadic.zeroTrit)
  ≡
  backward e Triadic.zeroTrit
fixedTargetPointForcesFixedSourcePoint e =
  trans
    (sym (leftInverse e (Ops.rotateTrit (backward e Triadic.zeroTrit))))
    (trans
      (cong (backward e)
        (trans
          (intertwines e (backward e Triadic.zeroTrit))
          (trans
            (cong Ops.reflectTrit (rightInverse e Triadic.zeroTrit))
            (sym (rightInverse e Triadic.zeroTrit)))))
      (leftInverse e (backward e Triadic.zeroTrit)))

noRotationReflectionEquivariantBijection :
  EquivariantBijection → ⊥
noRotationReflectionEquivariantBijection e =
  sourceRotationHasNoFixedPoint
    (backward e Triadic.zeroTrit)
    (fixedTargetPointForcesFixedSourcePoint e)

------------------------------------------------------------------------
-- The no-go is structural, not cardinal.

sourceCarrierCount : Nat
sourceCarrierCount = 3

targetCarrierCount : Nat
targetCarrierCount = 3

equalCarrierCounts : sourceCarrierCount ≡ targetCarrierCount
equalCarrierCounts = refl

record EqualCardinalityBoundary : Set where
  constructor equalCardinalityBoundary
  field
    equalCardinalitySelectsCanonicalMap : Bool
    equalCardinalitySelectsCanonicalMapIsFalse :
      equalCardinalitySelectsCanonicalMap ≡ false

    equalCardinalityForcesEquivariantIdentification : Bool
    equalCardinalityForcesEquivariantIdentificationIsFalse :
      equalCardinalityForcesEquivariantIdentification ≡ false

canonicalEqualCardinalityBoundary : EqualCardinalityBoundary
canonicalEqualCardinalityBoundary =
  equalCardinalityBoundary false refl false refl
