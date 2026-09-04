module DASHI.Physics.Plasma.MHDMagneticHelicityDirectionalVariationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as Normalized
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as Observer

------------------------------------------------------------------------
-- INVERSE-CURL SELF-ADJOINTNESS ON A TRANSVERSE FOURIER MODE
------------------------------------------------------------------------

vectorPotentialSelfAdjoint :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.Transverse E k u →
  Helical.Transverse E k v →
  C3.hermitianPairing3
    (Observer.magneticVectorPotentialMode E S k u) v
  ≡
  C3.hermitianPairing3
    u (Observer.magneticVectorPotentialMode E S k v)
vectorPotentialSelfAdjoint {F = F} E I S L k u v transverseU transverseV =
  trans
    (Scaling.hermitianPairingScaleLeft inverseC
      (Normalized.normalizedCurl E S k u) v)
    (trans
      (cong
        (λ first → C3.complexMultiply first
          (C3.hermitianPairing3
            (Normalized.normalizedCurl E S k u) v))
        (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))
      (trans
        (cong (C3.complexMultiply inverseC)
          (trans
            (Scaling.hermitianPairingScaleLeft inverseC
              (Helical.curlSymbol E k u) v)
            (trans
              (cong
                (λ first → C3.complexMultiply first
                  (C3.hermitianPairing3 (Helical.curlSymbol E k u) v))
                (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))
              (cong (C3.complexMultiply inverseC)
                (Helical.curlSymbolSelfAdjointOnTransverse
                  L k u v transverseU transverseV)))))
        (trans
          (sym
            (Scaling.complexMultiplyAssociative
              inverseC inverseC
              (C3.hermitianPairing3 u (Helical.curlSymbol E k v))))
          (trans
            (cong (C3.complexMultiply inverseC)
              (sym
                (Scaling.hermitianPairingScaleRight inverseC
                  u (Helical.curlSymbol E k v))))
            (sym
              (Scaling.hermitianPairingScaleRight inverseC
                u (Normalized.normalizedCurl E S k v)))))))
  where
  inverseC = C3.realEmbed F (Helical.inverseModeNorm S k)

------------------------------------------------------------------------
-- QUADRATIC DIRECTIONAL VARIATION
------------------------------------------------------------------------

magneticHelicityDirectionalVariation :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
magneticHelicityDirectionalVariation E S k magnetic tangent =
  C3.complexAdd
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (Observer.magneticVectorPotentialMode E S k magnetic)))
    (C3.complexRealPart
      (C3.hermitianPairing3 magnetic
        (Observer.magneticVectorPotentialMode E S k tangent)))

magneticHelicityVariationSymmetricForm :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (magnetic tangent : C3.Complex3 F) →
  Helical.Transverse E k magnetic →
  Helical.Transverse E k tangent →
  magneticHelicityDirectionalVariation E S k magnetic tangent
  ≡
  C3.complexAdd
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (Observer.magneticVectorPotentialMode E S k magnetic)))
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (Observer.magneticVectorPotentialMode E S k magnetic)))
magneticHelicityVariationSymmetricForm
    E I S L k magnetic tangent transverseMagnetic transverseTangent =
  cong
    (C3.complexAdd
      (C3.complexRealPart
        (C3.hermitianPairing3 tangent
          (Observer.magneticVectorPotentialMode E S k magnetic))))
    (trans
      (cong C3.complexRealPart
        (vectorPotentialSelfAdjoint
          E I S L k magnetic tangent transverseMagnetic transverseTangent))
      (cong C3.complexRealPart
        (sym
          (C3.hermitianPairingConjugateSymmetric
            tangent
            (Observer.magneticVectorPotentialMode E S k magnetic)))))

record MagneticHelicityVariationBoundary : Set where
  constructor magnetic-helicity-variation-boundary
  field
    inverseCurlSelfAdjointOnTransverseOwned : Bool
    inverseCurlSelfAdjointOnTransverseOwnedIsTrue :
      inverseCurlSelfAdjointOnTransverseOwned ≡ true

    magneticHelicityVariationNeedsInductionTangent : Bool
    magneticHelicityVariationNeedsInductionTangentIsTrue :
      magneticHelicityVariationNeedsInductionTangent ≡ true

    energyCrossHelicityZeroAloneClosesMagneticHelicity : Bool
    energyCrossHelicityZeroAloneClosesMagneticHelicityIsFalse :
      energyCrossHelicityZeroAloneClosesMagneticHelicity ≡ false

canonicalMagneticHelicityVariationBoundary : MagneticHelicityVariationBoundary
canonicalMagneticHelicityVariationBoundary =
  magnetic-helicity-variation-boundary true refl true refl false refl
