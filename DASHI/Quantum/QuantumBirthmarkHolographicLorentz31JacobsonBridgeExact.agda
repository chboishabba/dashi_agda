{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicLorentz31JacobsonBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Geometry.LargePosetContinuumLorentz31 as Lorentz31
import DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact as Gravity
import DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact as SameObject

------------------------------------------------------------------------
-- HOLOGRAPHIC BOUNDARY -> 3+1 LOCAL HORIZON -> JACOBSON PAYMENT SURFACE
--
-- The large-poset owner supplies a typed 3+1 Lorentzian authority, including
-- one time direction and time orientability.  Jacobson's source boundary says
-- that an Einstein-equation equation-of-state derivation additionally requires
-- local-horizon thermodynamics.  This adapter records exactly those payments.
-- It does not derive Einstein's equation itself.
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
-- A boundary entropy theorem becomes relevant to Jacobson only after the
-- boundary state and local horizon section are explicitly identified on the
-- same physical carrier.  A p-adic or tensor-network boundary does not supply
-- that identification automatically.
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
    lorentz31SuppliesPhysicalSpacetimeCarrier : Bool
    oneTimeDirectionIsOwned : Bool
    holographicBoundaryIsNotAutomaticallyLocalRindlerHorizon : Bool
    areaLawDoesNotSupplyClausiusRelation : Bool
    birthmarkDoesNotSupplyClausiusRelation : Bool
    birthmarkDoesNotSupplyStressTensorHeatFluxWeld : Bool
    residualInformationDensityDoesNotSupplyEntropyAreaVariationWeld : Bool
    sameObjectHorizonAttachmentRequired : Bool
    einsteinEquationNotDerivedByThisAdapter : Bool

canonicalJacobsonCompositionBoundary : JacobsonCompositionBoundary
canonicalJacobsonCompositionBoundary =
  jacobsonCompositionBoundary true true true true true true true true true

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
