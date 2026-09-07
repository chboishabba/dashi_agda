module DASHI.Core.MechanismDiscriminationApplicationAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Core

------------------------------------------------------------------------
-- APPLICATION ATLAS
--
-- These are reusable circumstance templates, not domain facts.  They identify
-- the common theorem shape: coarse endpoint collision -> discriminating
-- coordinate -> residual -> dependency-scoped reopen.
------------------------------------------------------------------------

data CircumstanceClass : Set where
  biochemicalMechanism : CircumstanceClass
  engineeringFaultDiagnosis : CircumstanceClass
  softwareFailureDiagnosis : CircumstanceClass
  ecologicalCausalAttribution : CircumstanceClass
  financialModelDiscrimination : CircumstanceClass
  legalCausalExplanation : CircumstanceClass
  historicalProvenanceExplanation : CircumstanceClass
  sensorFusionDiagnosis : CircumstanceClass


record CircumstanceTemplate : Set where
  constructor circumstanceTemplate
  field
    circumstance : CircumstanceClass
    coarseEndpoint : String
    competingWorlds : String
    discriminatingCoordinates : String
    dependencyCarriers : String
    interventionOrValidation : String
    authorityBoundary : String

open CircumstanceTemplate public

biochemicalTemplate : CircumstanceTemplate
biochemicalTemplate = circumstanceTemplate
  biochemicalMechanism
  "same viability / biofilm endpoint"
  "distinct chemical, protein, regulatory, recovery or transport mechanisms"
  "matched chemistry, molecular-target, cell-state and phenotype coordinates"
  "compound identity -> target modification -> function -> cell state -> phenotype"
  "branch-selective perturbation/rescue on the same preparation and organism"
  "related-source mechanism is a candidate, not target-system causal closure"

engineeringFaultTemplate : CircumstanceTemplate
engineeringFaultTemplate = circumstanceTemplate
  engineeringFaultDiagnosis
  "same alarm or degraded output"
  "distinct bearing, power, thermal, calibration or control-path faults"
  "vibration/current/temperature/calibration/control residuals"
  "component -> sensor -> controller -> output dependency graph"
  "controlled load, swap, calibration or isolation test"
  "one alarm does not identify one fault; safety authority remains domain-specific"

softwareFailureTemplate : CircumstanceTemplate
softwareFailureTemplate = circumstanceTemplate
  softwareFailureDiagnosis
  "same exception, timeout or wrong output"
  "distinct dependency, configuration, data, concurrency or environment causes"
  "trace, dependency version, configuration, input and timing coordinates"
  "module/config/data dependency graph"
  "minimal reproduction, dependency substitution or controlled configuration change"
  "log similarity is not proof of identical root cause"

ecologicalTemplate : CircumstanceTemplate
ecologicalTemplate = circumstanceTemplate
  ecologicalCausalAttribution
  "same population or ecosystem endpoint"
  "distinct habitat, predation, disease, climate, nutrient or sampling mechanisms"
  "matched environmental, demographic, pathogen, trophic and sampling coordinates"
  "driver -> organism/community -> measured endpoint graph"
  "natural experiment, intervention, temporal panel or matched comparator"
  "correlation and endpoint coincidence do not establish one ecological cause"

financialTemplate : CircumstanceTemplate
financialTemplate = circumstanceTemplate
  financialModelDiscrimination
  "same return, drawdown or portfolio loss"
  "distinct exposure, liquidity, volatility, concentration, execution or data-model explanations"
  "factor exposure, volume/liquidity, volatility, execution and data-quality coordinates"
  "data -> model -> position/exposure -> execution -> portfolio endpoint"
  "out-of-sample test, stress scenario, alternate model or execution decomposition"
  "same P&L does not identify a unique causal model; this is not investment advice"

legalTemplate : CircumstanceTemplate
legalTemplate = circumstanceTemplate
  legalCausalExplanation
  "same legal outcome or institutional effect"
  "distinct doctrinal gate, evidence, procedure, authority or implementation pathways"
  "authority, evidential, procedural, comparator and distributional coordinates"
  "source authority -> legal rule/gate -> decision -> institutional effect"
  "matched comparator, appellate authority, record audit or procedural counterfactual"
  "outcome does not prove motive; legal authority and inference remain separately typed"

historicalTemplate : CircumstanceTemplate
historicalTemplate = circumstanceTemplate
  historicalProvenanceExplanation
  "same surviving narrative or capability discontinuity"
  "distinct source-loss, custody, reorganisation, succession, codification or access mechanisms"
  "event-time possession, custody, source provenance, organisational and succession coordinates"
  "source/custody -> carrier -> transmission -> observed historical record"
  "new archival source, custody record, event-time evidence or matched chronology"
  "absence of a surviving record is not proof of deliberate suppression or targeting"

sensorFusionTemplate : CircumstanceTemplate
sensorFusionTemplate = circumstanceTemplate
  sensorFusionDiagnosis
  "same fused estimate"
  "distinct sensor bias, dropout, calibration, environmental or model-assumption states"
  "per-sensor residual, calibration, covariance/dependency and environment coordinates"
  "sensor -> calibration -> fusion -> estimate graph"
  "holdout sensor, recalibration, independent reference or controlled perturbation"
  "same fused output does not imply same latent sensor state"

record ApplicationAtlasBoundary : Set where
  constructor applicationAtlasBoundary
  field
    genericShapeTransfersDomainAuthorityAutomatically : Bool
    genericShapeTransfersDomainAuthorityAutomaticallyIsFalse :
      genericShapeTransfersDomainAuthorityAutomatically ≡ false

    sameEndpointCollisionIsReusableAcrossDomains : Bool
    sameEndpointCollisionIsReusableAcrossDomainsIsTrue :
      sameEndpointCollisionIsReusableAcrossDomains ≡ true

    selectiveReopeningPatternIsReusableAcrossDomains : Bool
    selectiveReopeningPatternIsReusableAcrossDomainsIsTrue :
      selectiveReopeningPatternIsReusableAcrossDomains ≡ true

    eachDomainStillNeedsItsOwnEvidenceAndValidationSemantics : Bool
    eachDomainStillNeedsItsOwnEvidenceAndValidationSemanticsIsTrue :
      eachDomainStillNeedsItsOwnEvidenceAndValidationSemantics ≡ true

canonicalApplicationAtlasBoundary : ApplicationAtlasBoundary
canonicalApplicationAtlasBoundary =
  applicationAtlasBoundary false refl true refl true refl true refl

-- Explicitly consume the domain-neutral model-discrimination boundary.
existingGenericBoundary : Core.ModelDiscriminationBoundary
existingGenericBoundary = Core.canonicalModelDiscriminationBoundary
