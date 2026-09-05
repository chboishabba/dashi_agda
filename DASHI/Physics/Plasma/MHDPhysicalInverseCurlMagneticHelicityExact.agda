module DASHI.Physics.Plasma.MHDPhysicalInverseCurlMagneticHelicityExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as InverseReality
import DASHI.Physics.Closure.NSTriadKNHelicalModeNormSquareActionRound126Exact as CurlLinear
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as Linear
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut

------------------------------------------------------------------------
-- PHYSICAL INVERSE-CURL OBSERVER
------------------------------------------------------------------------

physicalVectorPotential :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F
physicalVectorPotential {F = F} E I k magnetic =
  C3.complex3Scale
    (C3.realEmbed F (C3.inverseNormSquared I k))
    (Helical.curlSymbol E k magnetic)

physicalMagneticHelicityMode :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex F
physicalMagneticHelicityMode E I k magnetic =
  C3.complexRealPart
    (C3.hermitianPairing3 magnetic
      (physicalVectorPotential E I k magnetic))

physicalVectorPotentialReality :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (magnetic : C3.Complex3 F) →
  physicalVectorPotential E I (Z3.negateMode k)
    (C3.complex3Conjugate magnetic)
  ≡ C3.complex3Conjugate
      (physicalVectorPotential E I k magnetic)
physicalVectorPotentialReality {F = F} E I S L k magnetic =
  trans
    (cong₂ C3.complex3Scale
      (cong (C3.realEmbed F)
        (InverseReality.inverseNormSquaredEven E I k))
      (Helical.curlSymbolRealityCompatible L k magnetic))
    (sym
      (trans
        (Scaling.complex3ConjugateScale
          (C3.realEmbed F (C3.inverseNormSquared I k))
          (Helical.curlSymbol E k magnetic))
        (cong
          (λ scalar →
            C3.complex3Scale scalar
              (C3.complex3Conjugate (Helical.curlSymbol E k magnetic)))
          (C3.realEmbedConjugate F (C3.inverseNormSquared I k)))))

physicalVectorPotentialSelfAdjoint :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.Transverse E k u →
  Helical.Transverse E k v →
  C3.hermitianPairing3 (physicalVectorPotential E I k u) v
  ≡ C3.hermitianPairing3 u (physicalVectorPotential E I k v)
physicalVectorPotentialSelfAdjoint {F = F} E I S L k u v transverseU transverseV =
  trans
    (Scaling.hermitianPairingScaleLeft inverseC
      (Helical.curlSymbol E k u) v)
    (trans
      (cong
        (λ first →
          C3.complexMultiply first
            (C3.hermitianPairing3 (Helical.curlSymbol E k u) v))
        (C3.realEmbedConjugate F (C3.inverseNormSquared I k)))
      (trans
        (cong (C3.complexMultiply inverseC)
          (Helical.curlSymbolSelfAdjointOnTransverse
            L k u v transverseU transverseV))
        (sym
          (Scaling.hermitianPairingScaleRight inverseC
            u (Helical.curlSymbol E k v)))))
  where
  inverseC = C3.realEmbed F (C3.inverseNormSquared I k)

complex3ScaleOne :
  ∀ {r : Level} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Scale (C3.complexOne F) value ≡ value
complex3ScaleOne (C3.complex3 x y z) =
  Field.complex3Ext
    (Hermitian.complexMultiplyOneLeft x)
    (Hermitian.complexMultiplyOneLeft y)
    (Hermitian.complexMultiplyOneLeft z)

physicalVectorPotentialIsCurlInverse :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  (magnetic : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  Helical.curlSymbol E k (physicalVectorPotential E I k magnetic)
  ≡ magnetic
physicalVectorPotentialIsCurlInverse {F = F}
    E I S L k nonzero magnetic transverse =
  trans
    (CurlLinear.curlSymbolScale E k inverseC
      (Helical.curlSymbol E k magnetic))
    (trans
      (cong (C3.complex3Scale inverseC)
        (Helical.curlSymbolSquaredOnTransverse L k magnetic transverse))
      (trans
        (Linear.complex3ScaleAssociative inverseC normC magnetic)
        (trans
          (cong
            (λ coefficient → C3.complex3Scale coefficient magnetic)
            productIsOne)
          (complex3ScaleOne magnetic))))
  where
  inverse = C3.inverseNormSquared I k
  norm = C3.normSquared I k
  inverseC = C3.realEmbed F inverse
  normC = C3.realEmbed F norm

  productIsOne :
    C3.complexMultiply inverseC normC ≡ C3.complexOne F
  productIsOne =
    trans
      (LerayOut.realEmbedMultiply inverse norm)
      (cong (C3.realEmbed F) (C3.inverseLaw I k nonzero))

record PhysicalInverseCurlBoundary : Set where
  constructor physical-inverse-curl-boundary
  field
    inverseCurlUsesPhysicalInverseSquare : Bool
    inverseCurlUsesPhysicalInverseSquareIsTrue :
      inverseCurlUsesPhysicalInverseSquare ≡ true

    inverseCurlFourierRealityOwned : Bool
    inverseCurlFourierRealityOwnedIsTrue :
      inverseCurlFourierRealityOwned ≡ true

    inverseCurlSelfAdjointOwned : Bool
    inverseCurlSelfAdjointOwnedIsTrue : inverseCurlSelfAdjointOwned ≡ true

    inverseCurlActuallyInvertsCurlOnNonzeroTransverseModes : Bool
    inverseCurlActuallyInvertsCurlOnNonzeroTransverseModesIsTrue :
      inverseCurlActuallyInvertsCurlOnNonzeroTransverseModes ≡ true

    helicalInverseRadiusIsDefinitionOfPhysicalObserver : Bool
    helicalInverseRadiusIsDefinitionOfPhysicalObserverIsFalse :
      helicalInverseRadiusIsDefinitionOfPhysicalObserver ≡ false

canonicalPhysicalInverseCurlBoundary : PhysicalInverseCurlBoundary
canonicalPhysicalInverseCurlBoundary =
  physical-inverse-curl-boundary true refl true refl true refl true refl false refl
