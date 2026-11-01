module DASHI.Physics.Closure.NSWall1CanonicalAmplitudeProfile where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSWall1CanonicalModePacket
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier

------------------------------------------------------------------------
-- Exact finite-support background amplitude profile on the canonical packet.
------------------------------------------------------------------------

record CanonicalAmplitudeCoefficients
    {s : Level}
    (Scalar : Set s) : Set (lsuc s) where
  field
    amplitude100 : Scalar
    amplitude010 : Scalar
    amplitude001 : Scalar

open CanonicalAmplitudeCoefficients public

canonicalBackgroundAmplitude :
  ∀ {s}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar)
    (E : ExactFourierEvaluation Scalar A) →
  CanonicalAmplitudeCoefficients Scalar →
  FourierMode → Scalar
canonicalBackgroundAmplitude A E C k =
  add A
    (multiply A
      (modeDelta E k p100)
      (amplitude100 C))
    (add A
      (multiply A
        (modeDelta E k p010)
        (amplitude010 C))
      (multiply A
        (modeDelta E k p001)
        (amplitude001 C)))

record CanonicalAmplitudeSupportLaws
    {s : Level}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar)
    (E : ExactFourierEvaluation Scalar A)
    (C : CanonicalAmplitudeCoefficients Scalar) : Set (lsuc s) where
  field
    delta100At100 : modeDelta E p100 p100 ≡ one A
    delta010At010 : modeDelta E p010 p010 ≡ one A
    delta001At001 : modeDelta E p001 p001 ≡ one A

    delta100At010 : modeDelta E p010 p100 ≡ zero A
    delta100At001 : modeDelta E p001 p100 ≡ zero A
    delta010At100 : modeDelta E p100 p010 ≡ zero A
    delta010At001 : modeDelta E p001 p010 ≡ zero A
    delta001At100 : modeDelta E p100 p001 ≡ zero A
    delta001At010 : modeDelta E p010 p001 ≡ zero A

open CanonicalAmplitudeSupportLaws public
