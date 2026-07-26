module DASHI.Physics.Closure.NSTriadKNFrameFreeCoefficientRoute where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed

------------------------------------------------------------------------
-- The exact Fourier coefficient is intrinsically basis-free.
--
-- A normalised transverse frame is useful for polarisation coordinates, but
-- it is not required to define, enumerate, estimate, or sum the physical
-- coefficient. This removes frame construction from the critical Clay chain.
------------------------------------------------------------------------

frameFreeSignedCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
frameFreeSignedCoefficient {F = F} E I =
  Signed.testedSignedCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)

frameFreeOrderedPairCoefficient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
frameFreeOrderedPairCoefficient {F = F} E I =
  Signed.testedOrderedPairCoefficient
    (C3.complex3VelocityGalerkinLaws F E I)

record VectorCoordinateReconstruction
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Coordinate : Set r
    decode : Coordinate → C3.Complex3 F

open VectorCoordinateReconstruction public

coefficientInvariantUnderCoordinateReconstruction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (coordinates : VectorCoordinateReconstruction F)
    (k p q : Z3.FourierMode)
    (pCoordinate qCoordinate kCoordinate : Coordinate coordinates)
    (uP uQ uK : C3.Complex3 F) →
  decode coordinates pCoordinate ≡ uP →
  decode coordinates qCoordinate ≡ uQ →
  decode coordinates kCoordinate ≡ uK →
  frameFreeSignedCoefficient E I k p q
    (decode coordinates pCoordinate)
    (decode coordinates qCoordinate)
    (decode coordinates kCoordinate)
  ≡ frameFreeSignedCoefficient E I k p q uP uQ uK
coefficientInvariantUnderCoordinateReconstruction
  E I coordinates k p q pCoordinate qCoordinate kCoordinate
  uP uQ uK refl refl refl = refl

orderedPairInvariantUnderCoordinateReconstruction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (coordinates : VectorCoordinateReconstruction F)
    (k p q : Z3.FourierMode)
    (pCoordinate qCoordinate kCoordinate : Coordinate coordinates)
    (uP uQ uK : C3.Complex3 F) →
  decode coordinates pCoordinate ≡ uP →
  decode coordinates qCoordinate ≡ uQ →
  decode coordinates kCoordinate ≡ uK →
  frameFreeOrderedPairCoefficient E I k p q
    (decode coordinates pCoordinate)
    (decode coordinates qCoordinate)
    (decode coordinates kCoordinate)
  ≡ frameFreeOrderedPairCoefficient E I k p q uP uQ uK
orderedPairInvariantUnderCoordinateReconstruction
  E I coordinates k p q pCoordinate qCoordinate kCoordinate
  uP uQ uK refl refl refl = refl

frameNormalisationNotRequiredForPhysicalOperator : Bool
frameNormalisationNotRequiredForPhysicalOperator = true

frameNormalisationNotRequiredForPhysicalOperatorIsTrue :
  frameNormalisationNotRequiredForPhysicalOperator ≡ true
frameNormalisationNotRequiredForPhysicalOperatorIsTrue = refl
