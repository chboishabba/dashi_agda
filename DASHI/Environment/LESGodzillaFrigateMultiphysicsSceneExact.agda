module DASHI.Environment.LESGodzillaFrigateMultiphysicsSceneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalWorldEngineRTXCrossPollinationExact as World
import DASHI.Environment.LESMultiphysicsFidelityEscalationExact as Fidelity
import DASHI.Environment.LESVFXPhysicalOperationsExact as VFX
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Laws.PhysicalLawAtlas as Laws

------------------------------------------------------------------------
-- GODZILLA / FRIGATE SCENE AS A MULTIPHYSICS STRESS TEST
--
-- Fictional scene semantics are deliberately separated from physical model
-- authority.  The point of the fixture is to force one world state to retain
-- all exchanges that a convincing physically based VFX shot may need.
------------------------------------------------------------------------

data SceneBody : Set where
  creatureBody : SceneBody
  frigateHull : SceneBody
  frigateInternalStructure : SceneBody
  oceanBody : SceneBody
  atmosphereBody : SceneBody

data InteractionFamily : Set where
  creatureHullContact : InteractionFamily
  hullWaterHydrodynamics : InteractionFamily
  hullHydrostatics : InteractionFamily
  freeSurfaceWake : InteractionFamily
  creatureAirAerodynamics : InteractionFamily
  sprayFoamBubbles : InteractionFamily
  hullStructuralDeformation : InteractionFamily
  hullDamageOrFracture : InteractionFamily
  acousticShockAndRadiation : InteractionFamily
  electrostaticOrEM : InteractionFamily
  opticalAndVolumetricAppearance : InteractionFamily

record CreatureHullContactReceipt : Set₁ where
  constructor creature-hull-contact-receipt
  field
    contactGeometryReference : String
    nonpenetrationReference : String
    normalReactionReference : String
    tangentialFrictionReference : String
    impulseMomentumReference : String
    torqueAngularMomentumReference : String
    hullConstitutiveReference : String
    localStressStrainReference : String
    failureCriterionReference : String
    energyDissipationReference : String

open CreatureHullContactReceipt public

record HullWaterResistanceReceipt : Set₁ where
  constructor hull-water-resistance-receipt
  field
    fluidReduction : Fluid.FluidReductionReceipt
    submergedGeometryReference : String
    freeSurfaceReference : String
    hydrostaticPressureReference : String
    buoyancyReference : String
    viscousStressReference : String
    pressureDragReference : String
    waveMakingReference : String
    wakeVorticityReference : String
    addedMassReference : String
    slammingOrImpactReference : String
    cavitationReference : String
    momentumExchangeReference : String
    energyDissipationReference : String

open HullWaterResistanceReceipt public

record CreatureAirResistanceReceipt : Set₁ where
  constructor creature-air-resistance-receipt
  field
    fluidReduction : Fluid.FluidReductionReceipt
    creatureSurfaceReference : String
    pressureDragReference : String
    skinFrictionReference : String
    separatedWakeReference : String
    turbulenceReference : String
    compressibilityRegimeReference : String
    aeroacousticReference : String
    heatTransferReference : String

open CreatureAirResistanceReceipt public

record SprayFoamSecondaryPhaseReceipt : Set₁ where
  constructor spray-foam-secondary-phase-receipt
  field
    carrierFluidReference : String
    interfaceBreakupReference : String
    dropletOrBubbleSourceReference : String
    sizeDistributionReference : String
    dragCouplingReference : String
    evaporationOrCondensationReference : String
    coalescenceBreakupReference : String
    opticalScatteringReference : String
    returnToCarrierReference : String
    validationReference : String

open SprayFoamSecondaryPhaseReceipt public

------------------------------------------------------------------------
-- Ordinary static/electromagnetic effects use the existing U(1) socket.
------------------------------------------------------------------------

data EMSceneEffect : Set where
  noneResolved : EMSceneEffect
  triboelectricContactCharge : EMSceneEffect
  conductiveChargeRelaxation : EMSceneEffect
  lightningOrAtmosphericField : EMSceneEffect
  inductionOrCurrentEffect : EMSceneEffect
  instrumentOrRadarCoupling : EMSceneEffect

record SceneElectromagneticReceipt : Set₁ where
  constructor scene-electromagnetic-receipt
  field
    applicationReduction : EM.U1ApplicationReduction
    effect : EMSceneEffect
    chargeGenerationReference : String
    conductivityReference : String
    chargeRelaxationReference : String
    sourceCurrentReference : String
    fieldBoundaryReference : String
    LorentzCouplingReference : String
    measurementOrValidationReference : String

open SceneElectromagneticReceipt public

------------------------------------------------------------------------
-- One same-world fixture.
------------------------------------------------------------------------

record GodzillaFrigateWorldFixture
    (world : World.LESWorldEngineCarrier) : Set₁ where
  constructor godzilla-frigate-world-fixture
  field
    operationStep : VFX.VFXCoupledStep

    contact : CreatureHullContactReceipt
    waterResistance : HullWaterResistanceReceipt
    airResistance : CreatureAirResistanceReceipt
    secondaryWaterPhases : SprayFoamSecondaryPhaseReceipt
    electromagnetism : SceneElectromagneticReceipt

    sameCreatureStateReference : String
    sameHullStateReference : String
    sameOceanStateReference : String
    sameAtmosphereStateReference : String
    sameSpaceTimeReference : String

    gravityReference : String
    rigidBodyMotionReference : String
    structuralDynamicsReference : String
    freeSurfaceHydrodynamicsReference : String
    acousticReference : String
    renderingReference : String

    localPhysicsEscalation : InteractionFamily → Fidelity.PhysicsBackendOwner
    localEscalationReason : InteractionFamily → Fidelity.FidelityReason

    momentumLedgerReference : String
    energyLedgerReference : String
    massLedgerReference : String
    chargeLedgerReference : String
    numericalResidualReference : String
    shotValidationReference : String

open GodzillaFrigateWorldFixture public

------------------------------------------------------------------------
-- Law-owner references already present in the repository.
------------------------------------------------------------------------

newtonOwner : Laws.CanonicalPhysicalLaw
newtonOwner = Laws.newtonMomentumLaw

momentumBalanceOwner : Laws.CanonicalPhysicalLaw
momentumBalanceOwner = Laws.momentumBalanceLaw

energyBalanceOwner : Laws.CanonicalPhysicalLaw
energyBalanceOwner = Laws.energyBalanceLaw

elasticityOwner : Laws.CanonicalPhysicalLaw
elasticityOwner = Laws.hookeElasticityLaw

fluidOwner : Laws.CanonicalPhysicalLaw
fluidOwner = Laws.navierStokesWeakLaw

acousticOwner : Laws.CanonicalPhysicalLaw
acousticOwner = Laws.acousticLimitLaw

maxwellOwner : Laws.CanonicalPhysicalLaw
maxwellOwner = Laws.inhomogeneousMaxwellLaw

lorentzOwner : Laws.CanonicalPhysicalLaw
lorentzOwner = Laws.lorentzForceLaw

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data HullResistanceIsSingleDragCoefficient : Set where
hullResistanceIsNotSingleDragCoefficient : HullResistanceIsSingleDragCoefficient → ⊥
hullResistanceIsNotSingleDragCoefficient ()

data WakeIsOnlyVisualParticleTrail : Set where
wakeIsNotOnlyVisualParticleTrail : WakeIsOnlyVisualParticleTrail → ⊥
wakeIsNotOnlyVisualParticleTrail ()

data StaticElectricityRequiresYangMills : Set where
staticElectricityDoesNotRequireYangMills : StaticElectricityRequiresYangMills → ⊥
staticElectricityDoesNotRequireYangMills ()

data U1ElectromagnetismIsNonAbelianYM : Set where
u1ElectromagnetismIsNotNonAbelianYM : U1ElectromagnetismIsNonAbelianYM → ⊥
u1ElectromagnetismIsNotNonAbelianYM ()

data ContactSolverAloneDeterminesHullFailure : Set where
contactSolverAloneDoesNotDetermineHullFailure : ContactSolverAloneDeterminesHullFailure → ⊥
contactSolverAloneDoesNotDetermineHullFailure ()

data RenderedFoamCertifiesTwoPhaseFlow : Set where
renderedFoamDoesNotCertifyTwoPhaseFlow : RenderedFoamCertifiesTwoPhaseFlow → ⊥
renderedFoamDoesNotCertifyTwoPhaseFlow ()
