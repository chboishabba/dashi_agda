module DASHI.Physics.Plasma.MHDMagneticHelicityHelicalWeightBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.MHDHelicalCoefficientAnatomyExact as H

------------------------------------------------------------------------
-- MAGNETIC HELICITY: DISTINCT HELICAL-WEIGHT CONSUMER
--
-- In a helical Fourier basis, magnetic helicity is not the same quadratic
-- observer as total energy or cross helicity.  The mode contribution carries
-- a helicity-sign / radius weight (schematically s_k / |k| times |b_k|^2,
-- modulo the concrete normalization and complex pairing convention).
--
-- Therefore the Elsasser plus/minus energy cancellation route cannot close
-- magnetic helicity by itself.
------------------------------------------------------------------------

record MagneticHelicityWeight {r : _} (F : C3.RealField r) : Set r where
  constructor magnetic-helicity-weight
  field
    weight : H.BinarySign → C3.Carrier F → C3.Carrier F
    inverseRadiusNormalizationReceipt : Set
    helicalSignOrientationReceipt : Set
    gaugeOrPeriodicDomainReceipt : Set
    weightReference : String

open MagneticHelicityWeight public

record MagneticHelicityTriadConsumer {r : _} (F : C3.RealField r) : Set r where
  constructor magnetic-helicity-triad-consumer
  field
    weights : MagneticHelicityWeight F
    k p q : H.HelicalMHDMode F
    weightedKVariation : C3.Carrier F
    weightedPVariation : C3.Carrier F
    weightedQVariation : C3.Carrier F
    literalMagneticAmplitudeVariationReceipt : Set
    sameLiteralTriadReceipt : Set
    weightedCyclicCancellation : Set
    consumerReference : String

open MagneticHelicityTriadConsumer public

record MagneticHelicityBidiBoundary : Set where
  constructor magnetic-helicity-bidi-boundary
  field
    energyCrossHelicityElsasserBalanceClosesMagneticHelicity : Bool
    energyCrossHelicityElsasserBalanceClosesMagneticHelicityIsFalse :
      energyCrossHelicityElsasserBalanceClosesMagneticHelicity ≡ false

    magneticHelicityNeedsHelicalRadiusWeight : Bool
    magneticHelicityNeedsHelicalRadiusWeightIsTrue :
      magneticHelicityNeedsHelicalRadiusWeight ≡ true

    magneticHelicityWeightIsGaugeFreeInEveryDomain : Bool
    magneticHelicityWeightIsGaugeFreeInEveryDomainIsFalse :
      magneticHelicityWeightIsGaugeFreeInEveryDomain ≡ false

    weightedCyclicReceiptRequired : Bool
    weightedCyclicReceiptRequiredIsTrue :
      weightedCyclicReceiptRequired ≡ true

canonicalMagneticHelicityBidiBoundary : MagneticHelicityBidiBoundary
canonicalMagneticHelicityBidiBoundary =
  magnetic-helicity-bidi-boundary false refl true refl false refl true refl
