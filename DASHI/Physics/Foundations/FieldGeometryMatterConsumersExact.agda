{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterConsumersExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger
import DASHI.Physics.Foundations.ControlledPhysicalTransitionExact as Control
import DASHI.Physics.Foundations.PhysicalResidualPromotionExact as Promotion

------------------------------------------------------------------------
-- FOUR MECHANISM-NEUTRAL CONSUMERS
--
-- These are thin cross-domain adapters.  Open sibling PRs are referenced by
-- provenance strings rather than imported, so this master-based tranche does
-- not acquire unmerged compile-time dependencies.
------------------------------------------------------------------------

record QuantumMaterialEntropyAdapter : Set where
  constructor quantum-material-entropy-adapter
  field
    physicalOwnerReference : String
    geometryControl : Control.ControlCoordinate
    spectralStateReference : String
    degeneracyStateReference : String
    entropyObservationReference : String
    valleyC3PhysicalIdentificationPaid : Bool
    bandShapeIdentifiesMechanism : Bool
    quantumGeometryImpliesCaloricUtility : Bool

open QuantumMaterialEntropyAdapter public

canonicalQuantumMaterialEntropyAdapter : QuantumMaterialEntropyAdapter
canonicalQuantumMaterialEntropyAdapter =
  quantum-material-entropy-adapter
    "Twistronics relative-registration / flat-band owners; literal MATBG weld remains open"
    (Control.control-coordinate "twist/strain/gate/filling" "u_QM(t)" "sample-specific calibration required")
    "A(k,omega)/band-state consumer"
    "state-count/degeneracy consumer"
    "S(T,n,strain,B) consumer"
    false false false

record ProgrammableThermodynamicCycleAdapter : Set where
  constructor programmable-thermodynamic-cycle-adapter
  field
    physicalOwnerReference : String
    controlPath : Control.ControlledPhysicalTransition
    entropyLedger : Ledger.EntropyLedger
    energyLedger : Ledger.EnergyLedger
    workReference : String
    heatReference : String
    lossReference : String
    cycleClosurePaid : Bool
    geometryCaloricUtilityPaid : Bool

open ProgrammableThermodynamicCycleAdapter public

canonicalProgrammableThermodynamicCycleAdapter : ProgrammableThermodynamicCycleAdapter
canonicalProgrammableThermodynamicCycleAdapter =
  programmable-thermodynamic-cycle-adapter
    "MAGNOTHERM PR #1158 remains authoritative for material/device facts"
    Control.canonicalControlledTransition
    Ledger.canonicalEntropyLedger
    Ledger.canonicalEnergyLedger
    "control-conjugate work"
    "useful heat transfer"
    "hysteresis/relaxation/parasitic loss"
    false false

record EMBodyForceMomentumAdapter : Set where
  constructor em-body-force-momentum-adapter
  field
    physicalOwnerReference : String
    chargeDensityReference : String
    electricFieldReference : String
    currentDensityReference : String
    magneticFieldReference : String
    bodyForceReference : String
    fieldWorkReference : String
    boundaryMomentumFluxReference : String
    momentumLedger : Ledger.MomentumLedger
    confinementMechanismDistinct : Bool
    nozzleMechanismDistinct : Bool
    hypersonicFlowMechanismDistinct : Bool
    efficiencyMustBeCalibratedPerSystem : Bool

open EMBodyForceMomentumAdapter public

canonicalEMBodyForceMomentumAdapter : EMBodyForceMomentumAdapter
canonicalEMBodyForceMomentumAdapter =
  em-body-force-momentum-adapter
    "fusion-propulsion PR #1126 / confinement PR #1096 / future hypersonic-MHD owner"
    "rho_e" "E" "J" "B"
    "f_EM = rho_e E + J x B"
    "P_field = integral J dot E"
    "boundary momentum flux"
    Ledger.canonicalMomentumLedger
    true true true true

record ThrustNuisanceFibre : Set where
  constructor thrust-nuisance-fibre
  field
    thermalExpansionOrStrain : Bool
    pressureOrBuoyancy : Bool
    outgassing : Bool
    vibration : Bool
    supportsOrCables : Bool
    electrostaticCoupling : Bool
    magneticOrLorentzCoupling : Bool
    radiationPressure : Bool
    convection : Bool
    facilityCoupling : Bool
    sensorDrift : Bool

open ThrustNuisanceFibre public

canonicalThrustNuisanceFibre : ThrustNuisanceFibre
canonicalThrustNuisanceFibre =
  thrust-nuisance-fibre
    true true true true true true true true true true true

record PrecisionThrustResidualAdapter : Set where
  constructor precision-thrust-residual-adapter
  field
    physicalOwnerReference : String
    momentumLedger : Ledger.MomentumLedger
    residualCandidate : Promotion.AnomalousMomentumCandidate
    nuisanceFibre : ThrustNuisanceFibre
    declaredNuisanceFibrePresent : Bool
    residualIsMechanismNeutral : Bool
    gravityNeedsIndependentConsumer : Bool

open PrecisionThrustResidualAdapter public

canonicalPrecisionThrustResidualAdapter : PrecisionThrustResidualAdapter
canonicalPrecisionThrustResidualAdapter =
  precision-thrust-residual-adapter
    "precision-thrust/exotic-gravity same-object consumer"
    Ledger.canonicalMomentumLedger
    Promotion.canonicalAnomalousMomentumCandidate
    canonicalThrustNuisanceFibre
    true true true

------------------------------------------------------------------------
-- ROCKETDYNE QUALIFICATION GRAMMAR
------------------------------------------------------------------------

record QualificationTransferGrammar : Set where
  constructor qualification-transfer-grammar
  field
    environment : String
    materialAndCoating : String
    processHistory : String
    geometryAndLoad : String
    exposure : String
    inspection : String
    outcome : String
    qualification : String
    sameObjectEvidenceRequired : Bool

open QualificationTransferGrammar public

canonicalQualificationTransferGrammar : QualificationTransferGrammar
canonicalQualificationTransferGrammar =
  qualification-transfer-grammar
    "environment"
    "material/coating"
    "manufacturing/process history"
    "geometry/load"
    "exposure"
    "inspection"
    "outcome"
    "qualification decision"
    true

record ConsumerCrossDomainBoundary : Set where
  constructor consumer-cross-domain-boundary
  field
    sameBodyForceFormDoesNotIdentifyMechanism : Bool
    sameControlShapeDoesNotIdentifyMechanism : Bool
    sameEntropyShapeDoesNotIdentifyMaterial : Bool
    rocketdyneValuesDoNotTransfer : Bool
    rocketdyneFailureCauseDoesNotTransfer : Bool
    externalSiblingPRReferenceDoesNotCreateSameObjectPayment : Bool

open ConsumerCrossDomainBoundary public

canonicalConsumerBoundary : ConsumerCrossDomainBoundary
canonicalConsumerBoundary =
  consumer-cross-domain-boundary true true true true true true
