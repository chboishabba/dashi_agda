module DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExperimentLanguageExact as Language

------------------------------------------------------------------------
-- SOURCE-BOUNDED ACQUISITION RECEIPTS
------------------------------------------------------------------------

record RatioEvidence : Set where
  constructor ratio-evidence
  field
    sourceLabel : String
    doi : String
    sampleDescription : String
    cannabisMeanGram : String
    tobaccoMeanGram : String
    cannabisToTobaccoRatio : String
    observedRatioRange : String
    portableToAllUsers : Bool
open RatioEvidence public

hindocha2017Baseline : RatioEvidence
hindocha2017Baseline = ratio-evidence
  "Hindocha, Freeman, Curran 2017 Anatomy of a Joint"
  "10.1089/can.2017.0024"
  "24 recreational cannabis+tobacco co-users; Roll-a-Joint baseline actual weights"
  "0.14 g"
  "0.35 g"
  "0.53:1"
  "0.05:1 to 1.42:1"
  false

record AustralianUseEvidence : Set where
  constructor australian-use-evidence
  field
    sourceLabel : String
    doi : String
    finding : String
    tobaccoMassMeasured : Bool
    exactRatioPaid : Bool
open AustralianUseEvidence public

australiaJointMass2023 : AustralianUseEvidence
australiaJointMass2023 = australian-use-evidence
  "How much cannabis is used in a joint in Australia?"
  "10.1111/dar.13747"
  "Australian participants showed wide cannabis-mass variation across joints, spliffs and cones; spliff cannabis mass range 0.12-1.21 g"
  false
  false

record CoUsePrevalenceEvidence : Set where
  constructor co-use-prevalence-evidence
  field
    sourceLabel : String
    australiaMixedTobaccoPercent : String
    englandMixedTobaccoPercent : String
    usaMixedTobaccoPercent : String
    canadaMixedTobaccoPercent : String
    provesRatio : Bool
open CoUsePrevalenceEvidence public

itc2018CoUse : CoUsePrevalenceEvidence
itc2018CoUse = co-use-prevalence-evidence
  "ITC Four Country Smoking and Vaping Survey, cannabis+tobacco co-use analysis"
  "86.0%"
  "90.4%"
  "22.3%"
  "38.5%"
  false

------------------------------------------------------------------------
-- MACHINE PROTOCOL RECEIPTS
------------------------------------------------------------------------

record MachinePuffProtocol : Set where
  constructor machine-puff-protocol
  field
    protocolLabel : String
    puffVolumeMl : Nat
    puffDurationSeconds : Nat
    puffIntervalSeconds : Nat
    ventilationBlocked : Bool
    directlyUsedForCannabisComparison : Bool
    humanTopographyIdentity : Bool
    sourceNote : String
open MachinePuffProtocol public

healthCanadaIntenseComparator : MachinePuffProtocol
healthCanadaIntenseComparator = machine-puff-protocol
  "Health Canada Intense-compatible comparator"
  55 2 30 true true false
  "A 2019 marijuana-versus-tobacco mainstream-smoke comparison used 55 mL / 2 s / 30 s under identical testing conditions; this is a standardized machine regime, not a claim that all users inhale this way."

record LegacyCannabisTransferProtocol : Set where
  constructor legacy-cannabis-transfer-protocol
  field
    sourceLabel : String
    cannabisMassGram : String
    drawRateLPerMin : String
    ignitionSchedule : String
    replicateCountPerDevice : Nat
    exactHumanPuffVolumeControlled : Bool
open LegacyCannabisTransferProtocol public

sullivan2013Protocol : LegacyCannabisTransferProtocol
sullivan2013Protocol = legacy-cannabis-transfer-protocol
  "Sullivan, Elzinga, Raber 2013 pesticide transfer in cannabis smoke"
  "approximately 0.45 g"
  "1.2 L/min"
  "3 s lighter pass at 15 s intervals while vacuum applied"
  3
  false

------------------------------------------------------------------------
-- SAME-OBJECT MATERIAL / ALIQUOT LEDGER
------------------------------------------------------------------------

data Arm : Set where
  cannabisOnly tobaccoOnly mixed : Arm

record SourceMaterial : Set where
  constructor source-material
  field
    materialId : String
    materialClass : String
    homogenisationReceipt : String
    preBurnResiduePanelReceipt : String
    moistureReceipt : String
open SourceMaterial public

record ThreeArmAliquot : Set where
  constructor three-arm-aliquot
  field
    arm : Arm
    cannabisSourceId : String
    tobaccoSourceId : String
    cannabisMassMg : Nat
    tobaccoMassMg : Nat
    replicateBlock : String
    blindedSampleId : String
    sameSourceObjectsAcrossArms : Bool
open ThreeArmAliquot public

canonicalCannabisSource : SourceMaterial
canonicalCannabisSource = source-material
  "C-SRC-001"
  "homogenised dried cannabis flower"
  "same homogenised source split across C and CT arms"
  "declared analyte panel + LOQ + matrix recovery before combustion"
  "moisture measured before mass-normalised allocation"

canonicalTobaccoSource : SourceMaterial
canonicalTobaccoSource = source-material
  "T-SRC-001"
  "homogenised roll-your-own tobacco"
  "same homogenised source split across T and CT arms"
  "declared analyte panel + LOQ + matrix recovery before combustion"
  "moisture measured before mass-normalised allocation"

-- A source-bounded first fixture approximates the Hindocha 2017 actual mean
-- ratio using 140 mg cannabis : 350 mg tobacco.  This is a calibration fixture,
-- not a universal real-world spliff composition.

cArmPrototype : ThreeArmAliquot
cArmPrototype = three-arm-aliquot
  cannabisOnly "C-SRC-001" "none" 140 0 "fit-block-A" "C-A1" true

tArmPrototype : ThreeArmAliquot
tArmPrototype = three-arm-aliquot
  tobaccoOnly "none" "T-SRC-001" 0 350 "fit-block-A" "T-A1" true

ctArmPrototype : ThreeArmAliquot
ctArmPrototype = three-arm-aliquot
  mixed "C-SRC-001" "T-SRC-001" 140 350 "fit-block-A" "CT-A1" true

------------------------------------------------------------------------
-- OBSERVATION VECTOR
------------------------------------------------------------------------

record ObservationVector : Set where
  constructor observation-vector
  field
    sourceParentResidues : String
    mainstreamSmokeParentResidues : String
    thermalTransformationProducts : String
    nicotineMarker : String
    cannabinoidMarker : String
    totalParticulateMatter : String
    gasPhaseCollection : String
    particulatePhaseCollection : String
    puffCount : String
    massBurned : String
    uncertaintyReceipt : String
open ObservationVector public

canonicalObservationVector : ObservationVector
canonicalObservationVector = observation-vector
  "same analytes measured in each source before burn; include pesticide/PGR targets and matrix-specific LOQs"
  "same parent analytes quantified in mainstream smoke/condensate for C, T and CT"
  "non-targeted or declared targeted thermal-product lane retained separately from parent recovery"
  "nicotine concentration / yield as tobacco-source and transfer marker"
  "THC/THCA or agreed cannabinoid marker as cannabis-source and transfer marker"
  "TPM or collected aerosol mass"
  "gas-phase trap / bag metadata"
  "filter/pad/condensate metadata"
  "machine puff count per specimen"
  "starting and post-burn material mass"
  "technical replicate, blank, spike/recovery, calibration and held-out block metadata"

------------------------------------------------------------------------
-- RESIDUAL / INTERACTION CONTRACT
------------------------------------------------------------------------

record MixedInteractionResidual : Set where
  constructor mixed-interaction-residual
  field
    normalizationBasis : String
    additiveNull : String
    residualDefinition : String
    parentResidueResidual : String
    thermalProductResidual : String
    particlePhaseResidual : String
    acceptanceRule : String
open MixedInteractionResidual public

canonicalMixedResidual : MixedInteractionResidual
canonicalMixedResidual = mixed-interaction-residual
  "mass-normalise C and T contributions to the exact cannabis/tobacco masses used in CT"
  "Q_CT = scaled(Q_C) + scaled(Q_T)"
  "R_mix = Q_CT - [scaled(Q_C) + scaled(Q_T)]"
  "compute analyte-wise parent-residue residuals with propagated uncertainty"
  "thermal products are a separate vector because a new product can appear even if parent balance looks additive"
  "gas/particle partitioning is retained as a coordinate rather than collapsed into total mass"
  "interaction is admitted only where a predeclared residual threshold / uncertainty rule is crossed; direction and magnitude retained"

------------------------------------------------------------------------
-- VALIDATION / REPLICATION SPLIT
------------------------------------------------------------------------

record ReplicateLedger : Set where
  constructor replicate-ledger
  field
    fittingReplicatesPerArm : Nat
    heldOutReplicatesPerArm : Nat
    randomisedRunOrder : Bool
    analystBlindSampleIds : Bool
    apparatusBlankRequired : Bool
    sourceBlankRequired : Bool
    sameObjectValidation : Bool
    validationRule : String
open ReplicateLedger public

prototypeReplicateLedger : ReplicateLedger
prototypeReplicateLedger = replicate-ledger
  3 3 true true true true true
  "estimate interaction/residual structure on fitting block; repeat the predeclared residual test unchanged on held-out aliquots from the same homogenised source objects"

------------------------------------------------------------------------
-- RATIO ESCALATION
------------------------------------------------------------------------

record RatioEscalationPolicy : Set where
  constructor ratio-escalation-policy
  field
    firstRatio : String
    sourceBounded : Bool
    ratioUniversal : Bool
    observedHumanRangeRetained : String
    escalationTrigger : String
    nextDesign : String
open RatioEscalationPolicy public

canonicalRatioEscalation : RatioEscalationPolicy
canonicalRatioEscalation = ratio-escalation-policy
  "0.53:1 cannabis:tobacco, implemented as 140 mg : 350 mg prototype masses"
  true false
  "Hindocha baseline actual range 0.05:1-1.42:1; qualitative work also shows users vary ratios by context/time"
  "if interaction sign/magnitude is ratio-sensitive or the single-ratio result cannot answer the declared deployment consumer"
  "mixture-ratio response series spanning source-supported tobacco-heavy through cannabis-heavy compositions"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data OneObservedRatioCreatesUniversalRatio : Set where
data StandardMachineRegimeCreatesHumanTopography : Set where
data ParentMassBalanceCreatesThermalProductCompleteness : Set where
data TechnicalReplicationCreatesPopulationGeneralisability : Set where
data CannabisOnlyTransferCreatesMixedTransfer : Set where

oneRatioNotUniversal : OneObservedRatioCreatesUniversalRatio → ⊥
oneRatioNotUniversal ()

machineNotHumanIdentity : StandardMachineRegimeCreatesHumanTopography → ⊥
machineNotHumanIdentity ()

parentBalanceNotThermalComplete : ParentMassBalanceCreatesThermalProductCompleteness → ⊥
parentBalanceNotThermalComplete ()

technicalReplicationNotPopulationGeneralisability : TechnicalReplicationCreatesPopulationGeneralisability → ⊥
technicalReplicationNotPopulationGeneralisability ()

cannabisOnlyDoesNotCreateMixedTransfer : CannabisOnlyTransferCreatesMixedTransfer → ⊥
cannabisOnlyDoesNotCreateMixedTransfer ()

record ThreeArmExecutionBoundary : Set where
  constructor three-arm-execution-boundary
  field
    ratioEvidencePaid : Bool
    sameObjectAliquotDesignPaid : Bool
    machineProtocolPaid : Bool
    observationVectorPaid : Bool
    residualContractPaid : Bool
    heldOutReplicationStructurePaid : Bool
    actualPhysicalExecutionPaid : Bool
    directMixedPesticideDatasetPaid : Bool
    humanDoseInferencePaid : Bool
open ThreeArmExecutionBoundary public

canonicalThreeArmExecutionBoundary : ThreeArmExecutionBoundary
canonicalThreeArmExecutionBoundary = three-arm-execution-boundary
  true true true true true true false false false
