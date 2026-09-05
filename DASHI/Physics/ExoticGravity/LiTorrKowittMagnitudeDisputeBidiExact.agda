module DASHI.Physics.ExoticGravity.LiTorrKowittMagnitudeDisputeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LT
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalHyperfabricExact as H

------------------------------------------------------------------------
-- LI--TORR / KOWITT MAGNITUDE DISPUTE
--
-- Source scope:
--   Li & Torr, Phys. Rev. B 46, 5489 (1992).
--   Mark Kowitt, Phys. Rev. B 49, 704 (1994),
--     DOI 10.1103/PhysRevB.49.704.
--
-- Kowitt does not refute the existence of ordinary weak-field
-- gravitomagnetism.  The criticism targets the claimed superconducting
-- magnitude enhancement: the interpretation of magnetic permeability and the
-- microscopic dynamics used to support that interpretation.
------------------------------------------------------------------------

record MagnitudeDisputeReceipt : Set where
  constructor magnitude-dispute-receipt
  field
    disputedObject : String
    liTorrProducer : String
    kowittCritique : String
    critiqueTargetsMagnitude : Bool
    critiqueTargetsMagnitudeIsTrue : critiqueTargetsMagnitude ≡ true
    critiqueTargetsPermeabilityInterpretation : Bool
    critiqueTargetsPermeabilityInterpretationIsTrue :
      critiqueTargetsPermeabilityInterpretation ≡ true
    critiqueTargetsMicroscopicDynamics : Bool
    critiqueTargetsMicroscopicDynamicsIsTrue :
      critiqueTargetsMicroscopicDynamics ≡ true

canonicalMagnitudeDisputeReceipt : MagnitudeDisputeReceipt
canonicalMagnitudeDisputeReceipt = magnitude-dispute-receipt
  "estimated superconducting gravitomagnetic response magnitude"
  "Li & Torr, Phys. Rev. B 46, 5489 (1992)"
  "Kowitt, Phys. Rev. B 49, 704 (1994)"
  true refl
  true refl
  true refl

------------------------------------------------------------------------
-- BIDI decomposition of the disputed inference.
--
-- A large predicted gravity-channel signal cannot be owned merely from the
-- existence of a superconducting phase plus ordinary GEM equations.  Reverse
-- proof search has to acquire the constitutive coefficient that carries the
-- enhancement and show that its microscopic interpretation is physically
-- admissible.
------------------------------------------------------------------------

record EnhancementBidiCutset : Set where
  constructor enhancement-bidi-cutset
  field
    weakFieldGEMProducerRequired : Bool
    weakFieldGEMProducerRequiredIsTrue : weakFieldGEMProducerRequired ≡ true

    superconductingResponseProducerRequired : Bool
    superconductingResponseProducerRequiredIsTrue :
      superconductingResponseProducerRequired ≡ true

    permeabilityMeaningWeldRequired : Bool
    permeabilityMeaningWeldRequiredIsTrue :
      permeabilityMeaningWeldRequired ≡ true

    microscopicCurrentModelRequired : Bool
    microscopicCurrentModelRequiredIsTrue :
      microscopicCurrentModelRequired ≡ true

    magnitudeScalingProducerRequired : Bool
    magnitudeScalingProducerRequiredIsTrue :
      magnitudeScalingProducerRequired ≡ true

canonicalEnhancementBidiCutset : EnhancementBidiCutset
canonicalEnhancementBidiCutset = enhancement-bidi-cutset
  true refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Semantic firewall: bulk Meissner-language permeability cannot silently be
-- promoted into a microscopic constitutive coefficient and then multiplied
-- into a gravity-channel enhancement.
------------------------------------------------------------------------

record PermeabilitySemanticBoundary : Set where
  constructor permeability-semantic-boundary
  field
    bulkMeissnerPermeabilityEqualsMicroscopicLocalPermeability : Bool
    bulkMeissnerPermeabilityEqualsMicroscopicLocalPermeabilityIsFalse :
      bulkMeissnerPermeabilityEqualsMicroscopicLocalPermeability ≡ false

    nearZeroBulkMuImpliesHugeGravityEnhancement : Bool
    nearZeroBulkMuImpliesHugeGravityEnhancementIsFalse :
      nearZeroBulkMuImpliesHugeGravityEnhancement ≡ false

    permeabilitySymbolReuseProvesSamePhysicalObject : Bool
    permeabilitySymbolReuseProvesSamePhysicalObjectIsFalse :
      permeabilitySymbolReuseProvesSamePhysicalObject ≡ false

canonicalPermeabilitySemanticBoundary : PermeabilitySemanticBoundary
canonicalPermeabilitySemanticBoundary =
  permeability-semantic-boundary false refl false refl false refl

------------------------------------------------------------------------
-- Common-object statement: the coupled-potential chart is historically
-- present even if the large enhancement does not survive the constitutive
-- critique.  This prevents an all-or-nothing collapse of the source.
------------------------------------------------------------------------

record SurvivingStructure : Set where
  constructor surviving-structure
  field
    combinedPotentialChartPresent : Bool
    combinedPotentialChartPresentIsTrue :
      combinedPotentialChartPresent ≡ true

    separateEMAndGravityResponseEquationsPresent : Bool
    separateEMAndGravityResponseEquationsPresentIsTrue :
      separateEMAndGravityResponseEquationsPresent ≡ true

    largeEnhancementEstablishedByThoseShapesAlone : Bool
    largeEnhancementEstablishedByThoseShapesAloneIsFalse :
      largeEnhancementEstablishedByThoseShapesAlone ≡ false

canonicalSurvivingStructure : SurvivingStructure
canonicalSurvivingStructure = surviving-structure true refl true refl false refl

------------------------------------------------------------------------
-- Hyperfabric interpretation of the disputed alpha.
------------------------------------------------------------------------

record EnhancementCoordinate : Set where
  constructor enhancement-coordinate
  field
    ordinaryResponse : String
    proposedConstitutiveFactor : String
    predictedGravityResidual : String
    departureChannel : H.DepartureChannel

liTorrEnhancementCoordinate : EnhancementCoordinate
liTorrEnhancementCoordinate = enhancement-coordinate
  "ordinary weak-field stress-energy / mass-current response"
  "superconducting permeability/current-model enhancement"
  "detectable gravitomagnetic or gravitoelectric field"
  H.coherentCurrentGravityCoupling

------------------------------------------------------------------------
-- Fail-closed promotion rule.
------------------------------------------------------------------------

record MagnitudePromotionBoundary : Set where
  constructor magnitude-promotion-boundary
  field
    historicalEquationShapeClosesMagnitude : Bool
    historicalEquationShapeClosesMagnitudeIsFalse :
      historicalEquationShapeClosesMagnitude ≡ false

    contestedConstitutiveCoefficientClosesMagnitude : Bool
    contestedConstitutiveCoefficientClosesMagnitudeIsFalse :
      contestedConstitutiveCoefficientClosesMagnitude ≡ false

    independentMagnitudeReceiptRequired : Bool
    independentMagnitudeReceiptRequiredIsTrue :
      independentMagnitudeReceiptRequired ≡ true

canonicalMagnitudePromotionBoundary : MagnitudePromotionBoundary
canonicalMagnitudePromotionBoundary =
  magnitude-promotion-boundary false refl false refl true refl
