module DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Jerzy J. Jasielec,
-- "Electrodiffusion Phenomena in Neuroscience and the Nernst-Planck-Poisson
-- Equations",
-- Electrochem 2(2) (2021), 197-215.
-- DOI: 10.3390/electrochem2020014.
--
-- SOURCE BOUNDARY
-- The cited review motivates the coupled Poisson/Nernst-Planck description of
-- ionic electrodiffusion and its neuroscience relevance.  The typed SI carrier,
-- reusable application sockets, fluid-advection extension and promotion
-- boundaries below are DASHI formal reconstruction/extensions.
------------------------------------------------------------------------

record IonicSpeciesState : Set₁ where
  constructor ionicSpeciesState
  field
    State : Set
    valence : Int
    concentrationScale : SI.DecimalScale
    diffusionScale : SI.DecimalScale
    fluxScale : SI.DecimalScale
    concentration : State → SI.Quantity SI.MolarConcentration concentrationScale
    diffusionCoefficient : State → SI.Quantity SI.DiffusionCoefficient diffusionScale

open IonicSpeciesState public

------------------------------------------------------------------------
-- Core Nernst-Planck split: diffusion + electric migration.
--
-- We deliberately keep the spatial differential operator and scalar arithmetic
-- behind an application-supplied FluxCarrier.  The exported flux itself is
-- nonetheless dimensioned as mol m^-2 s^-1, and a concrete instance must prove
-- that the total flux is the combination of the two source terms.
------------------------------------------------------------------------

record NernstPlanckFluxLaw
    (species : IonicSpeciesState)
    (field : EM.U1ElectromagneticFieldSocket) : Set₁ where
  constructor nernstPlanckFluxLaw
  field
    CoupledState : Set
    FluxCarrier : Set

    speciesState : CoupledState → State species
    fieldState : CoupledState → EM.FieldState field

    diffusiveFlux : CoupledState → FluxCarrier
    electricMigrationFlux : CoupledState → FluxCarrier
    combineFlux : FluxCarrier → FluxCarrier → FluxCarrier
    totalFlux : CoupledState → FluxCarrier

    totalFluxDecomposition :
      (state : CoupledState) →
      totalFlux state
      ≡ combineFlux (diffusiveFlux state) (electricMigrationFlux state)

    molarFluxDensity : FluxCarrier → SI.Quantity SI.MolarFluxDensity (fluxScale species)

    concentrationGradientReference : String
    electrochemicalMigrationReference : String
    temperatureReference : String
    constantsAndValenceReference : String
    validityRegimeReference : String

open NernstPlanckFluxLaw public

------------------------------------------------------------------------
-- Poisson/electrostatic coupling.
--
-- The strongest same-object weld available without inventing numeric field
-- arithmetic is to require the charge density produced from the ionic state to
-- equal the charge density carried by the electromagnetic field state.
------------------------------------------------------------------------

record PoissonChargeCoupling
    {species : IonicSpeciesState}
    {field : EM.U1ElectromagneticFieldSocket}
    (np : NernstPlanckFluxLaw species field) : Set₁ where
  constructor poissonChargeCoupling
  field
    ionicChargeDensity :
      (state : CoupledState np) →
      SI.Quantity SI.ChargeDensity (EM.chargeDensityScale field)

    ionicAndFieldChargeDensityAgree :
      (state : CoupledState np) →
      ionicChargeDensity state
      ≡ EM.chargeDensity field (fieldState np state)

    poissonEquationReference : String
    permittivityModelReference : String
    boundaryConditionReference : String

open PoissonChargeCoupling public

------------------------------------------------------------------------
-- Moving-fluid extension.
--
-- Classical PNP electrodiffusion in a static solvent does not by itself supply
-- fluid advection. LES needs a separate weld when water, sap, cytoplasm,
-- extracellular fluid or another moving medium advects ions.
------------------------------------------------------------------------

record AdvectiveElectrodiffusionExtension
    {species : IonicSpeciesState}
    {field : EM.U1ElectromagneticFieldSocket}
    (np : NernstPlanckFluxLaw species field) : Set₁ where
  constructor advectiveElectrodiffusionExtension
  field
    FluidState : Set
    velocityScale : SI.DecimalScale
    velocity : FluidState → SI.Quantity SI.Velocity velocityScale

    ExtendedState : Set
    npState : ExtendedState → CoupledState np
    fluidState : ExtendedState → FluidState

    ExtendedFluxCarrier : Set
    electrodiffusiveFlux : ExtendedState → ExtendedFluxCarrier
    advectiveFlux : ExtendedState → ExtendedFluxCarrier
    combineExtendedFlux : ExtendedFluxCarrier → ExtendedFluxCarrier → ExtendedFluxCarrier
    totalExtendedFlux : ExtendedState → ExtendedFluxCarrier

    totalExtendedFluxDecomposition :
      (state : ExtendedState) →
      totalExtendedFlux state
      ≡ combineExtendedFlux
          (electrodiffusiveFlux state)
          (advectiveFlux state)

    fluidReductionReference : String
    commonSpaceTimeReference : String
    advectionValidationReference : String

open AdvectiveElectrodiffusionExtension public

------------------------------------------------------------------------
-- Cross-domain applications share this physical seam, not one empirical model.
------------------------------------------------------------------------

data ElectrodiffusionApplication : Set where
  neuronalMembrane
  genericCellMembrane
  plantRootIonTransport
  fungalIonExchange
  soilPoreElectrochemistry
  aqueousEnvironmentalTransport
  : ElectrodiffusionApplication

record ElectrodiffusionApplicationReceipt : Set₁ where
  constructor electrodiffusionApplicationReceipt
  field
    application : ElectrodiffusionApplication
    species : IonicSpeciesState
    electromagneticField : EM.U1ElectromagneticFieldSocket
    fluxLaw : NernstPlanckFluxLaw species electromagneticField
    poissonCoupling : PoissonChargeCoupling fluxLaw
    membraneOrInterfaceReference : String
    constitutiveParameterAuthorityReference : String
    initialBoundaryConditionReference : String
    experimentalValidationReference : String

open ElectrodiffusionApplicationReceipt public

sourceDOI : String
sourceDOI = "10.3390/electrochem2020014"

record PNPElectrodiffusionBoundary : Set where
  constructor pnpElectrodiffusionBoundary
  field
    nernstEquationAloneIsNernstPlanckTransport : Bool
    nernstEquationAloneIsNernstPlanckTransportIsFalse :
      nernstEquationAloneIsNernstPlanckTransport ≡ false

    pnpAutomaticallySuppliesFluidAdvection : Bool
    pnpAutomaticallySuppliesFluidAdvectionIsFalse :
      pnpAutomaticallySuppliesFluidAdvection ≡ false

    onePNPParameterisationValidForAllApplications : Bool
    onePNPParameterisationValidForAllApplicationsIsFalse :
      onePNPParameterisationValidForAllApplications ≡ false

    sameSITypeImpliesSameConstitutiveParameter : Bool
    sameSITypeImpliesSameConstitutiveParameterIsFalse :
      sameSITypeImpliesSameConstitutiveParameter ≡ false

    pnpApplicationNeedsBoundaryAndValidationReceipts : Bool
    pnpApplicationNeedsBoundaryAndValidationReceiptsIsTrue :
      pnpApplicationNeedsBoundaryAndValidationReceipts ≡ true

canonicalPNPElectrodiffusionBoundary : PNPElectrodiffusionBoundary
canonicalPNPElectrodiffusionBoundary =
  pnpElectrodiffusionBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
