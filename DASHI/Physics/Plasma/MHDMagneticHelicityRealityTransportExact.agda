module DASHI.Physics.Plasma.MHDMagneticHelicityRealityTransportExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDPhysicalInverseCurlMagneticHelicityExact as InverseCurl
import DASHI.Physics.Plasma.MHDMagneticHelicityThreeLegBidiExact as ThreeLeg

------------------------------------------------------------------------
-- REALITY TRANSPORT OF THE PHYSICAL MAGNETIC-HELICITY OBSERVER
------------------------------------------------------------------------

physicalMagneticHelicityRealityInvariant :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (magnetic : C3.Complex3 F) →
  InverseCurl.physicalMagneticHelicityMode E I (Z3.negateMode k)
    (C3.complex3Conjugate magnetic)
  ≡ InverseCurl.physicalMagneticHelicityMode E I k magnetic
physicalMagneticHelicityRealityInvariant E I S L k magnetic =
  trans
    (cong C3.complexRealPart
      (cong
        (C3.hermitianPairing3 (C3.complex3Conjugate magnetic))
        (InverseCurl.physicalVectorPotentialReality E I S L k magnetic)))
    (trans
      (cong C3.complexRealPart
        (Field.hermitianConjugatePair magnetic vectorPotential))
      (trans
        (cong C3.complexRealPart
          (Field.hermitianConjugateSymmetry magnetic vectorPotential))
        (Hermitian.complexRealPartConjugateInvariant
          (C3.hermitianPairing3 magnetic vectorPotential))))
  where
  vectorPotential = InverseCurl.physicalVectorPotential E I k magnetic

------------------------------------------------------------------------
-- The complete quadratic directional variation is also reality-invariant.
------------------------------------------------------------------------

physicalMagneticHelicityVariationRealityInvariant :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (magnetic tangent : C3.Complex3 F) →
  ThreeLeg.physicalMagneticHelicityDirectionalVariation E I
    (Z3.negateMode k)
    (C3.complex3Conjugate magnetic)
    (C3.complex3Conjugate tangent)
  ≡ ThreeLeg.physicalMagneticHelicityDirectionalVariation E I
      k magnetic tangent
physicalMagneticHelicityVariationRealityInvariant E I S L k magnetic tangent =
  cong₂ C3.complexAdd firstTerm secondTerm
  where
  aMagnetic = InverseCurl.physicalVectorPotential E I k magnetic
  aTangent = InverseCurl.physicalVectorPotential E I k tangent

  firstTerm :
    C3.complexRealPart
      (C3.hermitianPairing3
        (C3.complex3Conjugate tangent)
        (InverseCurl.physicalVectorPotential E I (Z3.negateMode k)
          (C3.complex3Conjugate magnetic)))
    ≡ C3.complexRealPart
        (C3.hermitianPairing3 tangent aMagnetic)
  firstTerm =
    trans
      (cong C3.complexRealPart
        (cong
          (C3.hermitianPairing3 (C3.complex3Conjugate tangent))
          (InverseCurl.physicalVectorPotentialReality E I S L k magnetic)))
      (trans
        (cong C3.complexRealPart
          (Field.hermitianConjugatePair tangent aMagnetic))
        (trans
          (cong C3.complexRealPart
            (Field.hermitianConjugateSymmetry tangent aMagnetic))
          (Hermitian.complexRealPartConjugateInvariant
            (C3.hermitianPairing3 tangent aMagnetic))))

  secondTerm :
    C3.complexRealPart
      (C3.hermitianPairing3
        (C3.complex3Conjugate magnetic)
        (InverseCurl.physicalVectorPotential E I (Z3.negateMode k)
          (C3.complex3Conjugate tangent)))
    ≡ C3.complexRealPart
        (C3.hermitianPairing3 magnetic aTangent)
  secondTerm =
    trans
      (cong C3.complexRealPart
        (cong
          (C3.hermitianPairing3 (C3.complex3Conjugate magnetic))
          (InverseCurl.physicalVectorPotentialReality E I S L k tangent)))
      (trans
        (cong C3.complexRealPart
          (Field.hermitianConjugatePair magnetic aTangent))
        (trans
          (cong C3.complexRealPart
            (Field.hermitianConjugateSymmetry magnetic aTangent))
          (Hermitian.complexRealPartConjugateInvariant
            (C3.hermitianPairing3 magnetic aTangent))))

record MagneticHelicityRealityTransportBoundary : Set where
  constructor magnetic-helicity-reality-transport-boundary
  field
    observerRealityInvariantOwned : Bool
    observerRealityInvariantOwnedIsTrue : observerRealityInvariantOwned ≡ true

    variationRealityInvariantOwned : Bool
    variationRealityInvariantOwnedIsTrue : variationRealityInvariantOwned ≡ true

    realityInvarianceAloneProvesThreeLegZero : Bool
    realityInvarianceAloneProvesThreeLegZeroIsFalse :
      realityInvarianceAloneProvesThreeLegZero ≡ false

canonicalMagneticHelicityRealityTransportBoundary :
  MagneticHelicityRealityTransportBoundary
canonicalMagneticHelicityRealityTransportBoundary =
  magnetic-helicity-reality-transport-boundary true refl true refl false refl
