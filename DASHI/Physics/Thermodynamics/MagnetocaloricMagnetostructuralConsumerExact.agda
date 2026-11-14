module DASHI.Physics.Thermodynamics.MagnetocaloricMagnetostructuralConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE

------------------------------------------------------------------------
-- Magnetostructural / elasticity consumer.
--
-- First-order magnetocaloric materials may couple magnetic order, lattice
-- strain and stored elastic energy.  The bridge keeps the magnetic response
-- and mechanical response distinct while allowing a calibrated coupling to
-- feed fatigue/cracking and regenerator geometry integrity.
------------------------------------------------------------------------

record MagnetostructuralBridge
  (M : MCE.MagnetocaloricMaterial)
  (E : Continuum.ElasticityLaw) : Set₁ where
  open MCE.MagnetocaloricMaterial M
  open Continuum.ElasticityLaw E
  field
    materialState : MaterialState
    deformation : Deformation
    elasticModulus : ElasticModulus

    MagneticStructuralOrderParameter : Set
    MagnetostrictiveCoupling : Set
    TransitionStrainEvidence : Set
    CyclicFatigueEvidence : Set
    CoatingStressTransferEvidence : Set

    magneticStructuralOrderParameter : MagneticStructuralOrderParameter
    magnetostrictiveCoupling : MagnetostrictiveCoupling
    transitionStrainEvidence : TransitionStrainEvidence
    cyclicFatigueEvidence : CyclicFatigueEvidence
    coatingStressTransferEvidence : CoatingStressTransferEvidence

    mechanicalEquilibrium : Equilibrium deformation
    materialStable : StableMaterial elasticModulus

record MagnetostructuralIntegrityProjection
  {M : MCE.MagnetocaloricMaterial}
  {E : Continuum.ElasticityLaw}
  (B : MagnetostructuralBridge M E) : Set₁ where
  field
    CrackRisk : Set
    ChannelGeometryChange : Set
    ThermalContactChange : Set
    MagneticResponseChange : Set

    crackRisk : CrackRisk
    channelGeometryChange : ChannelGeometryChange
    thermalContactChange : ThermalContactChange
    magneticResponseChange : MagneticResponseChange

    CouplingCalibrated : Set
    couplingCalibrated : CouplingCalibrated

record MagnetostructuralAuthorityBoundary : Set where
  constructor magnetostructural-authority-boundary
  field
    magneticTransitionDoesNotEqualMechanicalFailure : Bool
    elasticityInterfaceDoesNotSupplyMagnetostriction : Bool
    magnetostrictionRequiresMaterialCalibration : Bool
    coatingIntegrityRequiresInterfaceMechanics : Bool
    cyclicStrainCanFeedDegradationWithoutProvingLifetime : Bool

canonicalMagnetostructuralAuthorityBoundary : MagnetostructuralAuthorityBoundary
canonicalMagnetostructuralAuthorityBoundary =
  magnetostructural-authority-boundary true true true true true
