module DASHI.Physics.Closure.NSWall1CanonicalPolarizations where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier
open import DASHI.Physics.Closure.NSWall1CanonicalModePacket

------------------------------------------------------------------------
-- Explicit coordinate polarizations for the canonical six-mode packet.
------------------------------------------------------------------------

canonicalPolarization100 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization100 A = vec3 (zero A) (one A) (zero A)

canonicalPolarization010 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization010 A = vec3 (zero A) (zero A) (one A)

canonicalPolarization001 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization001 A = vec3 (one A) (zero A) (zero A)

canonicalPolarization110 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization110 A = vec3 (one A) (negate A (one A)) (zero A)

canonicalPolarization101 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization101 A = vec3 (one A) (zero A) (negate A (one A))

canonicalPolarization011 :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar → Vec3 Scalar
canonicalPolarization011 A = vec3 (zero A) (one A) (negate A (one A))

canonicalPolarization :
  ∀ {s} {Scalar : Set s} →
  ExactScalarAlgebra Scalar →
  (modeTag : Set) →
  (modeTag → Vec3 Scalar)
canonicalPolarization A modeTag = λ _ → vecZero A

record CanonicalPolarizationLaws
    {s : Level}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar) : Set (lsuc s) where
  field
    transverse100 :
      vecDot A (integerWaveVector A p100) (canonicalPolarization100 A) ≡ zero A
    transverse010 :
      vecDot A (integerWaveVector A p010) (canonicalPolarization010 A) ≡ zero A
    transverse001 :
      vecDot A (integerWaveVector A p001) (canonicalPolarization001 A) ≡ zero A
    transverse110 :
      vecDot A (integerWaveVector A p110) (canonicalPolarization110 A) ≡ zero A
    transverse101 :
      vecDot A (integerWaveVector A p101) (canonicalPolarization101 A) ≡ zero A
    transverse011 :
      vecDot A (integerWaveVector A p011) (canonicalPolarization011 A) ≡ zero A

open CanonicalPolarizationLaws public
