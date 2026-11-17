module DASHI.Physics.Motors.SmithFilsingerCloudCausalWeldExact where

-- Physical F14/F16 cause-chain boundary. NOT a rain simulator.
-- An atmospheric *observational association* does not license a directed
-- intervention-to-cloud-field arrow; that requires a separate experiment.
-- Keep local cold-pool change distinct from global top-of-atmosphere effect.
-- All physical arrows are indexed by a single source-selected field/port.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Physics.Motors.SmithFilsingerSunEarthCoupledSourceExact as Sun
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- The actual study is only an association, proved directly from the
-- original literature-provenance owner (not reclassified as intervention).
raindropStudyRemainsObservation :
  Sun.sourceTier Sun.electricFieldRaindrops2021
    ≡ Sun.observedNaturalAssociation
raindropStudyRemainsObservation = refl

coldPoolStudyRemainsObservation :
  Sun.sourceTier Sun.kirschColdPools2021
    ≡ Sun.observedNaturalAssociation
coldPoolStudyRemainsObservation = refl

-- Distinct formal evidence types for observational association and
-- intervention identification.
data CausalTier : Set where
  observationalAssociation independentlyControlledIntervention : CausalTier

associationIsNotIntervention :
  observationalAssociation ≡ independentlyControlledIntervention →
  Port.Contradiction
associationIsNotIntervention ()

-- A SAME-OBJECT receipt must carry the particular electrical/Maxwell
-- boundary and its source work accounting; otherwise an unrelated cloud
-- association could accidentally be attached to a different machine.
record OriginalCloudInterventionWeld
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (w : Weld.SignedSourceCycleWeld b f) : Set₂ where
  field
    ActualControllerIntervention : Set
    MeasuredCloudFieldResponse : Set
    ControlledDropletSizeResponse : Set
    ControlledPrecipitationChange : Set
    ControlledLocalColdPoolHeatBudget : Set

    -- The causal arrows are evidence-dependent: neither a rain paper nor
    -- an algebraic Poynting equation can construct these values.
    controllerToCloudField :
      ActualControllerIntervention → MeasuredCloudFieldResponse
    cloudFieldToDroplets :
      MeasuredCloudFieldResponse → ControlledDropletSizeResponse
    dropletsToRain :
      ControlledDropletSizeResponse → ControlledPrecipitationChange
    rainToLocalColdPool :
      ControlledPrecipitationChange → ControlledLocalColdPoolHeatBudget

    -- The intended controlled intervention must be provided separately;
    -- this field is NOT derived from observational field/rain correlations.
    controlledOriginalIntervention : ActualControllerIntervention

controlledLocalCoolingRequiresAllCausalArrows :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (w : Weld.SignedSourceCycleWeld b f)
  (c : OriginalCloudInterventionWeld b f w) →
  OriginalCloudInterventionWeld.ControlledLocalColdPoolHeatBudget c
controlledLocalCoolingRequiresAllCausalArrows b f w c =
  OriginalCloudInterventionWeld.rainToLocalColdPool c
    (OriginalCloudInterventionWeld.dropletsToRain c
      (OriginalCloudInterventionWeld.cloudFieldToDroplets c
        (OriginalCloudInterventionWeld.controllerToCloudField c
          (OriginalCloudInterventionWeld.controlledOriginalIntervention c))))

-- A successful local cold-pool effect alone is NOT a theorem about
-- global top-of-atmosphere cooling. Its additional work/energy budget,
-- radiative forcing and climate counterfactual remain separate.
record GlobalClimatePromotion
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (w : Weld.SignedSourceCycleWeld b f)
  (c : OriginalCloudInterventionWeld b f w) : Set₂ where
  field
    IndependentlyMeasuredRadiativeForcing : Set
    GlobalEnergyBalanceAndUncertainty : Set
    ControlledGlobalClimateEffect : Set
    forcing : IndependentlyMeasuredRadiativeForcing
    balance : GlobalEnergyBalanceAndUncertainty
    globalEffect : ControlledGlobalClimateEffect

-- A small finite two-world nonidentifiability theorem (NOT a model of
-- real raindrop physics). Both worlds look the same observationally,
-- but their INTERVENTION classification is provably different.
data ObservationalWorld : Set where
  commonForcingOnly fieldMediated : ObservationalWorld

data NaturalFieldRainObservation : Set where
  sameFieldAndRainAssociation : NaturalFieldRainObservation

naturalObservation : ObservationalWorld → NaturalFieldRainObservation
naturalObservation commonForcingOnly = sameFieldAndRainAssociation
naturalObservation fieldMediated = sameFieldAndRainAssociation

data ControlledRainEffect : Set where
  noControlledRainEffect controlledRainResponse : ControlledRainEffect

underControlledIntervention : ObservationalWorld → ControlledRainEffect
underControlledIntervention commonForcingOnly = noControlledRainEffect
underControlledIntervention fieldMediated = controlledRainResponse

effectsDiffer :
  noControlledRainEffect ≡ controlledRainResponse → Port.Contradiction
effectsDiffer ()

AssociationIdentifiesCausalIntervention : Set
AssociationIdentifiesCausalIntervention =
  (a b : ObservationalWorld) →
  naturalObservation a ≡ naturalObservation b →
  underControlledIntervention a ≡ underControlledIntervention b

observationalCloudRainAssociationDoesNotWeld :
  AssociationIdentifiesCausalIntervention → Port.Contradiction
observationalCloudRainAssociationDoesNotWeld infer =
  effectsDiffer (infer commonForcingOnly fieldMediated refl)

-- Final F14 admission is deliberately independent from cloud/rain research:
-- source-based original hardware, acoustic and electrical observations
-- plus the SAME-port physical Maxwell/signed-work weld are mandatory.
record OriginalElectricalRegimeWeld
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (w : Weld.SignedSourceCycleWeld b f) : Set₁ where
  field
    ActualPinCompleteCircuit : Set
    TimeAlignedElectricalSwitchAndVITrace : Set
    TimeAlignedAcousticStartHotNullOff : Set
    OneSelectedConstitutiveParameterSet : Set
    JointOriginalElectricalAcousticExplanation : Set

    pins : ActualPinCompleteCircuit
    trace : TimeAlignedElectricalSwitchAndVITrace
    acoustic : TimeAlignedAcousticStartHotNullOff
    parameters : OneSelectedConstitutiveParameterSet
    sameObjectExplanation : JointOriginalElectricalAcousticExplanation
