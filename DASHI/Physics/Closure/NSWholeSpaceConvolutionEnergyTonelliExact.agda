module DASHI.Physics.Closure.NSWholeSpaceConvolutionEnergyTonelliExact where

------------------------------------------------------------------------
-- A / WHOLE-SPACE CONVOLUTION ENERGY FACTORISATION
--
-- Do NOT try to integrate the pairwise majorant on the full
-- (xi,eta-alpha,eta-beta) Gram-pair carrier.  Each summand then ignores one
-- free R^3 variable and the resulting positive majorant is not the correct
-- coherent object.
--
-- For the actual single convolution fibre the ordinary state-energy factor is
--
--   e(eta) e(xi-eta).
--
-- Fubini followed by the translation xi |-> xi-eta gives
--
--   integral_eta integral_xi e(eta)e(xi-eta)
--     = (integral e)^2.
--
-- Thus finite Fourier kinetic energy is already the correct integrability
-- currency for this product.  No L^4-frequency hypothesis is introduced.
--
-- The repository currently has no concrete Bishop/Lebesgue implementation of
-- Fubini/Tonelli.  This owner therefore isolates the exact selected standard-
-- analysis laws and proves the NS-specific factorisation from them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

record ConvolutionPoint : Set where
  constructor convolution-point
  field
    xi eta : Euclidean.R3Frequency

open ConvolutionPoint public

zeta : ConvolutionPoint → Euclidean.R3Frequency
zeta p = Euclidean.r3Subtract (xi p) (eta p)

record SelectedR3ConvolutionLebesgueAuthority
    (energyDensity : Euclidean.R3Frequency → BishopReal.ℝ) : Set₁ where
  field
    integralR3 :
      (Euclidean.R3Frequency → BishopReal.ℝ) → BishopReal.ℝ

    integralR6 :
      (ConvolutionPoint → BishopReal.ℝ) → BishopReal.ℝ

    IntegrableR3 :
      (Euclidean.R3Frequency → BishopReal.ℝ) → Set

    IntegrableR6 :
      (ConvolutionPoint → BishopReal.ℝ) → Set

    energyDensityIntegrable :
      IntegrableR3 energyDensity

    energyDensityNonnegative :
      (k : Euclidean.R3Frequency) →
      BishopReal.NonNegative (energyDensity k)

    convolutionProductIntegrable :
      IntegrableR6
        (λ p →
          BishopReal._*_
            (energyDensity (eta p))
            (energyDensity (zeta p)))

    -- Selected Fubini law on the literal convolution product.
    selectedFubini :
      BishopReal._≃_
        (integralR6
          (λ p →
            BishopReal._*_
              (energyDensity (eta p))
              (energyDensity (zeta p))))
        (integralR3
          (λ eta0 →
            integralR3
              (λ xi0 →
                BishopReal._*_
                  (energyDensity eta0)
                  (energyDensity
                    (Euclidean.r3Subtract xi0 eta0)))))

    -- Translation invariance plus scalar pull-out for the inner xi integral.
    selectedTranslation :
      (eta0 : Euclidean.R3Frequency) →
      BishopReal._≃_
        (integralR3
          (λ xi0 →
            BishopReal._*_
              (energyDensity eta0)
              (energyDensity
                (Euclidean.r3Subtract xi0 eta0))))
        (BishopReal._*_
          (energyDensity eta0)
          (integralR3 energyDensity))

    -- Extensionality of the outer integral on the selected pair of functions.
    outerIntegralRespectsSelectedPointwise :
      ((eta0 : Euclidean.R3Frequency) →
        BishopReal._≃_
          (integralR3
            (λ xi0 →
              BishopReal._*_
                (energyDensity eta0)
                (energyDensity
                  (Euclidean.r3Subtract xi0 eta0))))
          (BishopReal._*_
            (energyDensity eta0)
            (integralR3 energyDensity))) →
      BishopReal._≃_
        (integralR3
          (λ eta0 →
            integralR3
              (λ xi0 →
                BishopReal._*_
                  (energyDensity eta0)
                  (energyDensity
                    (Euclidean.r3Subtract xi0 eta0)))))
        (integralR3
          (λ eta0 →
            BishopReal._*_
              (energyDensity eta0)
              (integralR3 energyDensity)))

    -- Scalar pull-out for the outer eta integral.
    selectedOuterScalar :
      BishopReal._≃_
        (integralR3
          (λ eta0 →
            BishopReal._*_
              (energyDensity eta0)
              (integralR3 energyDensity)))
        (BishopReal._*_
          (integralR3 energyDensity)
          (integralR3 energyDensity))

open SelectedR3ConvolutionLebesgueAuthority public

convolutionEnergyProduct :
  (energyDensity : Euclidean.R3Frequency → BishopReal.ℝ) →
  ConvolutionPoint → BishopReal.ℝ
convolutionEnergyProduct energyDensity p =
  BishopReal._*_
    (energyDensity (eta p))
    (energyDensity (zeta p))

convolutionEnergyFactorisation :
  (energyDensity : Euclidean.R3Frequency → BishopReal.ℝ) →
  (A : SelectedR3ConvolutionLebesgueAuthority energyDensity) →
  BishopReal._≃_
    (integralR6 A (convolutionEnergyProduct energyDensity))
    (BishopReal._*_
      (integralR3 A energyDensity)
      (integralR3 A energyDensity))
convolutionEnergyFactorisation energyDensity A =
  BishopP.≃-trans
    (selectedFubini A)
    (BishopP.≃-trans
      (outerIntegralRespectsSelectedPointwise A
        (selectedTranslation A))
      (selectedOuterScalar A))

record FiniteFourierEnergy
    (energyDensity : Euclidean.R3Frequency → BishopReal.ℝ)
    (A : SelectedR3ConvolutionLebesgueAuthority energyDensity) : Set where
  constructor finite-fourier-energy
  field
    energyMass : BishopReal.ℝ
    energyMassExact :
      BishopReal._≃_ energyMass (integralR3 A energyDensity)

open FiniteFourierEnergy public

convolutionEnergyEqualsEnergySquare :
  (energyDensity : Euclidean.R3Frequency → BishopReal.ℝ) →
  (A : SelectedR3ConvolutionLebesgueAuthority energyDensity) →
  (E : FiniteFourierEnergy energyDensity A) →
  BishopReal._≃_
    (integralR6 A (convolutionEnergyProduct energyDensity))
    (BishopReal._*_ (energyMass E) (energyMass E))
convolutionEnergyEqualsEnergySquare energyDensity A E =
  BishopP.≃-trans
    (convolutionEnergyFactorisation energyDensity A)
    (BishopP.*-cong
      (BishopP.≃-symm (energyMassExact E))
      (BishopP.≃-symm (energyMassExact E)))

singleConvolutionProductNeedsOnlyFiniteEnergy : Bool
singleConvolutionProductNeedsOnlyFiniteEnergy = true

frequencyL4HypothesisIntroduced : Bool
frequencyL4HypothesisIntroduced = false

fullGramPairPositiveMajorantIntegratedHere : Bool
fullGramPairPositiveMajorantIntegratedHere = false

freeEtaCoordinateIntroduced : Bool
freeEtaCoordinateIntroduced = false

concreteFubiniTonelliProvedHere : Bool
concreteFubiniTonelliProvedHere = false

clayPromotion : Bool
clayPromotion = false

singleConvolutionProductNeedsOnlyFiniteEnergyIsTrue :
  singleConvolutionProductNeedsOnlyFiniteEnergy ≡ true
singleConvolutionProductNeedsOnlyFiniteEnergyIsTrue = refl

frequencyL4HypothesisIntroducedIsFalse :
  frequencyL4HypothesisIntroduced ≡ false
frequencyL4HypothesisIntroducedIsFalse = refl

freeEtaCoordinateIntroducedIsFalse :
  freeEtaCoordinateIntroduced ≡ false
freeEtaCoordinateIntroducedIsFalse = refl

concreteFubiniTonelliProvedHereIsFalse :
  concreteFubiniTonelliProvedHere ≡ false
concreteFubiniTonelliProvedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
