{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicLorentz31JacobsonBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Geometry.LargePosetContinuumLorentz31 as Lorentz31
import DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact as Gravity
import DASHI.Physics.Closure.TemporalSheafProofObligations as Sheaf
import DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact as SameObject
import DASHI.Quantum.QuantumMereologySpacetimePromotionExact as SpacetimePromotion

------------------------------------------------------------------------
-- HOLOGRAPHIC BOUNDARY -> QUANTUM SPATIAL GEOMETRY -> SPACETIME ->
-- 3+1 LOCAL HORIZON -> JACOBSON PAYMENT SURFACE
--
-- The repo already owns an explicit promotion seam from entanglement-derived
-- spatial geometry into a spacetime sheaf, and separately a large-poset 3+1
-- Lorentzian authority.  Neither step is automatic.  Jacobson then requires
-- additional local-horizon thermodynamics.  This adapter records all three
-- payments without identifying them by prose.
------------------------------------------------------------------------

lorentz31HasOneTimeDirection :
  (authority : Lorentz31.LargePosetContinuumLorentz31Authority) →
  Lorentz31.continuumTimeDimension authority ≡ 1
lorentz31HasOneTimeDirection = Lorentz31.continuumTimeDimensionIsOne

record LocalHorizonThermodynamicPackage
    (authority : Lorentz31.LargePosetContinuumLorentz31Authority) : Set₁ where
  field
    HorizonSection : Set
    HeatFlux : Set
    Temperature : Set
    EntropyVariation : Set
    AreaVariation : Set
    StressFlux : Set

    localHorizonAttachment : Set
    localHorizonAttachmentProof : localHorizonAttachment

    localRindlerHorizonStructure : Set
    localRindlerHorizonStructureProof : localRindlerHorizonStructure

    unruhTemperatureIdentification : Set
    unruhTemperatureIdentificationProof : unruhTemperatureIdentification

    entropyAreaVariationWeld : Set
    entropyAreaVariationWeldProof : entropyAreaVariationWeld

    clausiusRelation : Set
    clausiusRelationProof : clausiusRelation

    heatFluxStressTensorWeld : Set
    heatFluxStressTensorWeldProof : heatFluxStressTensorWeld

    allLocalNullDirectionsCovered : Set
    allLocalNullDirectionsCoveredProof : allLocalNullDirectionsCovered

open LocalHorizonThermodynamicPackage public

------------------------------------------------------------------------
-- Same-object holographic-to-horizon attachment.
--
-- `QuantumMereologySpacetimePromotionExact` already makes the spatial->time
-- seam explicit through `SpacetimeSheafObligation`: same spatial carrier,
-- entanglement-distance agreement and spacetime gluing must be paid.  Here we
-- require the holographic boundary to land on that same spacetime/horizon
-- carrier before its entropy can participate in a Jacobson-style derivation.
------------------------------------------------------------------------

record HolographicHorizonSameObjectWeld
    (authority : Lorentz31.LargePosetContinuumLorentz31Authority)
    (thermo : LocalHorizonThermodynamicPackage authority) : Set₁ where
  field
    BoundaryState : Set
    boundaryState : BoundaryState

    boundaryEntropyData : SameObject.BoundaryEntropySameObjectData

    boundaryStateIsEntropyDataState : Set
    boundaryStateIsEntropyDataStateProof : boundaryStateIsEntropyDataState

    spacetimeSheaf : Sheaf.SpacetimeSheafObligation

    quantumMereologySpacetimePromotionReused : Set
    quantumMereologySpacetimePromotionReusedProof :
      quantumMereologySpacetimePromotionReused

    sameSpatialCarrier : Set
    sameSpatialCarrierProof : sameSpatialCarrier

    sameTemporalCarrier : Set
    sameTemporalCarrierProof : sameTemporalCarrier

    boundaryToHorizonSection : BoundaryState → HorizonSection thermo

    physicalBoundaryHorizonIdentification : Set
    physicalBoundaryHorizonIdentificationProof :
      physicalBoundaryHorizonIdentification

    boundaryEntropyVariationEqualsHorizonEntropyVariation : Set
    boundaryEntropyVariationEqualsHorizonEntropyVariationProof :
      boundaryEntropyVariationEqualsHorizonEntropyVariation

    holographicAreaMatchesHorizonAreaVariation : Set
    holographicAreaMatchesHorizonAreaVariationProof :
      holographicAreaMatchesHorizonAreaVariation

open HolographicHorizonSameObjectWeld public

record JacobsonCompositionBoundary : Set where
  constructor jacobsonCompositionBoundary
  field
    quantumMereologySpacetimePromotionOwnerReused : Bool
    spacetimeSheafObligationReused : Bool
    lorentz31SuppliesPhysicalSpacetimeCarrier : Bool
    oneTimeDirectionIsOwned : Bool
    holographicBoundaryIsNotAutomaticallyLocalRindlerHorizon : Bool
    spatialGeometryDoesNotAutomaticallySupplyTime : Bool
    spacetimeSheafDoesNotAutomaticallySupplyEinsteinDynamics : Bool
    areaLawDoesNotSupplyClausiusRelation : Bool
    birthmarkDoesNotSupplyClausiusRelation : Bool
    birthmarkDoesNotSupplyStressTensorHeatFluxWeld : Bool
    residualInformationDensityDoesNotSupplyEntropyAreaVariationWeld : Bool
    sameObjectHorizonAttachmentRequired : Bool
    einsteinEquationNotDerivedByThisAdapter : Bool

canonicalJacobsonCompositionBoundary : JacobsonCompositionBoundary
canonicalJacobsonCompositionBoundary =
  jacobsonCompositionBoundary
    true true true true true true true true true true true true true

------------------------------------------------------------------------
-- Max-cut readiness surface.
--
-- Once all local thermodynamic premises and a same-object holographic/horizon
-- weld are supplied, this record certifies that the ingredients expected by
-- the Jacobson source boundary have been assembled on one 3+1 carrier.  The
-- actual differential-geometric Einstein-equation derivation remains an
-- independent theorem obligation.
------------------------------------------------------------------------

record JacobsonReadySurface : Set₁ where
  field
    lorentzAuthority : Lorentz31.LargePosetContinuumLorentz31Authority
    horizonThermodynamics : LocalHorizonThermodynamicPackage lorentzAuthority
    holographicHorizonWeld :
      HolographicHorizonSameObjectWeld lorentzAuthority horizonThermodynamics

    timeDimensionIsOne :
      Lorentz31.continuumTimeDimension lorentzAuthority ≡ 1

    jacobsonSourceBoundaryReused : Gravity.EntropicGravityClaimBoundary

    einsteinEquationDerivation : Set
    einsteinEquationDerivationProof : einsteinEquationDerivation

open JacobsonReadySurface public

birthmarkDoesNotSupplyClausiusRelation : Bool
birthmarkDoesNotSupplyClausiusRelation = true

einsteinEquationNotDerivedByThisAdapter : Bool
einsteinEquationNotDerivedByThisAdapter = true
