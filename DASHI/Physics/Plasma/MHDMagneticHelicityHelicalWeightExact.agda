module DASHI.Physics.Plasma.MHDMagneticHelicityHelicalWeightExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as Observer

------------------------------------------------------------------------
-- EXACT HELICAL WEIGHT OF MAGNETIC HELICITY
------------------------------------------------------------------------

plusMagneticVectorPotentialWeight :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : Observer.ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Observer.magneticVectorPotentialMode E S k
    (Helical.helicalProjectorPlus E I S k value)
  ≡ C3.complex3Scale
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (Helical.helicalProjectorPlus E I S k value)
plusMagneticVectorPotentialWeight {F = F} E I S L k C value =
  cong
    (C3.complex3Scale
      (C3.realEmbed F (Helical.inverseModeNorm S k)))
    (Observer.normalizedCurlPlusIsIdentity E I S L k C value)

minusMagneticVectorPotentialWeight :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : Observer.ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Observer.magneticVectorPotentialMode E S k
    (Helical.helicalProjectorMinus E I S k value)
  ≡ C3.complex3Scale
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (C3.complex3Negate
        (Helical.helicalProjectorMinus E I S k value))
minusMagneticVectorPotentialWeight {F = F} E I S L k C value =
  cong
    (C3.complex3Scale
      (C3.realEmbed F (Helical.inverseModeNorm S k)))
    (Observer.normalizedCurlMinusIsNegation E I S L k C value)

plusMagneticHelicityWeight :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : Observer.ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Observer.magneticHelicityMode E S k
    (Helical.helicalProjectorPlus E I S k value)
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (C3.hermitianPairing3
        (Helical.helicalProjectorPlus E I S k value)
        (Helical.helicalProjectorPlus E I S k value)))
plusMagneticHelicityWeight {F = F} E I S L k C value =
  trans
    (cong C3.complexRealPart
      (cong
        (C3.hermitianPairing3
          (Helical.helicalProjectorPlus E I S k value))
        (plusMagneticVectorPotentialWeight E I S L k C value)))
    (cong C3.complexRealPart
      (Scaling.hermitianPairingScaleRight
        (C3.realEmbed F (Helical.inverseModeNorm S k))
        (Helical.helicalProjectorPlus E I S k value)
        (Helical.helicalProjectorPlus E I S k value)))

minusMagneticHelicityWeight :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : Observer.ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Observer.magneticHelicityMode E S k
    (Helical.helicalProjectorMinus E I S k value)
  ≡
  C3.complexRealPart
    (C3.complexNegate
      (C3.complexMultiply
        (C3.realEmbed F (Helical.inverseModeNorm S k))
        (C3.hermitianPairing3
          (Helical.helicalProjectorMinus E I S k value)
          (Helical.helicalProjectorMinus E I S k value))))
minusMagneticHelicityWeight {F = F} E I S L k C value =
  trans
    (cong C3.complexRealPart
      (cong
        (C3.hermitianPairing3
          (Helical.helicalProjectorMinus E I S k value))
        (minusMagneticVectorPotentialWeight E I S L k C value)))
    (trans
      (cong C3.complexRealPart
        (Scaling.hermitianPairingScaleRight
          (C3.realEmbed F (Helical.inverseModeNorm S k))
          (Helical.helicalProjectorMinus E I S k value)
          (C3.complex3Negate
            (Helical.helicalProjectorMinus E I S k value))))
      (cong C3.complexRealPart
        (trans
          (cong
            (C3.complexMultiply
              (C3.realEmbed F (Helical.inverseModeNorm S k)))
            (Additive.hermitianPairingNegateRight
              (Helical.helicalProjectorMinus E I S k value)
              (Helical.helicalProjectorMinus E I S k value)))
          (C3.complexNegateMultiplyRight
            (C3.realEmbed F (Helical.inverseModeNorm S k))
            (C3.hermitianPairing3
              (Helical.helicalProjectorMinus E I S k value)
              (Helical.helicalProjectorMinus E I S k value))))))

record ExactMagneticHelicityWeightBoundary : Set where
  constructor exact-magnetic-helicity-weight-boundary
  field
    plusWeightIsPositiveInverseRadius : Bool
    plusWeightIsPositiveInverseRadiusIsTrue :
      plusWeightIsPositiveInverseRadius ≡ true

    minusWeightIsNegativeInverseRadius : Bool
    minusWeightIsNegativeInverseRadiusIsTrue :
      minusWeightIsNegativeInverseRadius ≡ true

    weightDerivedFromInverseCurlRatherThanPostulated : Bool
    weightDerivedFromInverseCurlRatherThanPostulatedIsTrue :
      weightDerivedFromInverseCurlRatherThanPostulated ≡ true

canonicalExactMagneticHelicityWeightBoundary : ExactMagneticHelicityWeightBoundary
canonicalExactMagneticHelicityWeightBoundary =
  exact-magnetic-helicity-weight-boundary true refl true refl true refl
