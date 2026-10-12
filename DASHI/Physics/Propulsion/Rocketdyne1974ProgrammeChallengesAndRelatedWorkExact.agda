{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ProgrammeChallengesAndRelatedWorkExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROGRAMME CHALLENGES AND RELATED WORK
------------------------------------------------------------------------

data ChallengeDomain : Set where
  contamination valveReliability injectorFlow combustionStability
  thermalMargin structuralJoint maintainability massAndGeometry
  operatingEnvelope : ChallengeDomain

data ChallengeStatus : Set where
  observedProblem observedButSafeFunction designConstraint
  mitigationRequired lineageLesson designOpportunity : ChallengeStatus

record ProgrammeChallenge : Set where
  constructor programme-challenge
  field
    domain : ChallengeDomain
    status : ChallengeStatus
    challenge : String
    observedConsequence : String
    mitigationOrDesignResponse : String
    sourceReference : String
    same1974Programme : Bool

sandDustValveChallenge : ProgrammeChallenge
sandDustValveChallenge =
  programme-challenge
    valveReliability observedProblem
    "sand/dust entered the propulsion assembly during environmental exposure and migrated toward the bipropellant valve"
    "valve leakage/degradation; Rocketdyne calls particle migration to the valve potentially severe"
    "develop an environmentally robust valve, or protect/purge the engine before each mission"
    "R-9557-1 p.36 ENGINE DESIGN UPDATE; valve hardware from NASA/JSC NAS9-12996"
    true

orificePluggingChallenge : ProgrammeChallenge
orificePluggingChallenge =
  programme-challenge
    injectorFlow observedButSafeFunction
    "injector orifice plugging after environmental sand/dust exposure"
    "safe engine function retained, but mixture-ratio shifts could alter propellant consumption"
    "do not infer that simply reducing injector element count fixes the problem; largest hole was reported more susceptible"
    "R-9557-1 p.36 ENGINE DESIGN UPDATE"
    true

lowThrottleOscillationChallenge : ProgrammeChallenge
lowThrottleOscillationChallenge =
  programme-challenge
    combustionStability observedProblem
    "low-pressure throttle operation developed chamber-pressure oscillations"
    "intermittent ~110-Hz oscillations of about +/-15 psi near 102 psia and about +/-40 psi oscillations at 67 psia"
    "retain a bounded stable operating envelope and acquire full same-run dynamic data before modelling an instability boundary"
    "R-9557-1 p.36 off-limits throttle-mode results"
    true

brazeJointChallenge : ProgrammeChallenge
brazeJointChallenge =
  programme-challenge
    structuralJoint designConstraint
    "recent injector-to-beryllium-chamber braze required reusable vibration qualification"
    "100-mission-equivalent three-axis random-vibration campaign was used to test joint integrity"
    "retain measured strain and structural margin separately from actual flown missions"
    "NASA-CR-140308 abstract; R-9557-1 vibration simulator results"
    true

maintainabilityChallenge : ProgrammeChallenge
maintainabilityChallenge =
  programme-challenge
    maintainability designConstraint
    "100-flight / 10-year concept targeted no scheduled servicing or periodic replacement"
    "condition monitoring and visual inspection were still recommended for degradation detection and unscheduled maintenance"
    "fault detection/isolation + visual inspection + maintainable component interfaces"
    "R-9557-1 maintainability discussion and Table 2.0"
    true

weightReductionOpportunity : ProgrammeChallenge
weightReductionOpportunity =
  programme-challenge
    massAndGeometry designOpportunity
    "large measured thermal margin left the flightweight concept heavier than necessary"
    "programme analysis identified possible beryllium-mass reduction and a lower contraction ratio"
    "use test-correlated thermal analysis before removing mass or changing contraction ratio"
    "R-9557-1 p.36 ENGINE DESIGN UPDATE"
    true

------------------------------------------------------------------------
-- REPEATED VALVE FAILURE MECHANISM
------------------------------------------------------------------------

record ValveFailureObservation : Set where
  constructor valve-failure-observation
  field
    serial : String
    model : String
    contractOrigin : String
    priorExposure : String
    observedFailure : String
    inspectionFinding : String
    attributedMechanism : String
    sourceReference : String

valveSN003Failure : ValveFailureObservation
valveSN003Failure =
  valve-failure-observation
    "S/N 003"
    "Moog 54X107A"
    "NASA/JSC residual hardware from NAS9-12996"
    "extensive hot-fire and environmental test programme before delivery to Rocketdyne"
    "gross oxidizer leakage after Rocketdyne environmental testing"
    "gross amounts of fine-textured sand found during Moog manifold inspection"
    "sand/dust/salt introduced through the nozzle migrated through the injector during random vibration and abraded the oxidizer-side Teflon seal"
    "R-9557-1 p.33 Propellant Valve Failures; R-9557 Table 22"

valveSN005Failure : ValveFailureObservation
valveSN005Failure =
  valve-failure-observation
    "S/N 005"
    "Moog 54X107A"
    "second programme-support valve"
    "Rocketdyne environmental exposure sequence"
    "leakage became progressively worse as environmental testing progressed"
    "reported same failure mode as S/N 003"
    "environmental contaminant migration / seal abrasion mechanism repeated"
    "R-9557-1 p.33 Propellant Valve Failures"

record RepeatedValveFailure : Set where
  constructor repeated-valve-failure
  field
    first : ValveFailureObservation
    second : ValveFailureObservation
    sameValveModel : Bool
    sameReportedFailureMode : Bool
    repeatedMechanismStrengthensComponentAttribution : Bool
    establishesFleetFailureRate : Bool

valveSerialFailurePair : RepeatedValveFailure
valveSerialFailurePair =
  repeated-valve-failure
    valveSN003Failure valveSN005Failure true true true false

sandAbradedTeflonSealMechanism : String
sandAbradedTeflonSealMechanism =
  "wet environmental contaminants -> particle migration during vibration -> oxidizer-side Teflon seat/seal abrasion -> excessive leakage"

------------------------------------------------------------------------
-- PREDECESSOR / RELATED INTEREGEN WORK
------------------------------------------------------------------------

record RelatedProgramme : Set where
  constructor related-programme
  field
    name : String
    architecture : String
    thrustClass : String
    reportedLesson : String
    relationshipToR9557 : String
    sourceReference : String
    sameHardware : Bool

vikingOperatingEnvelopeLineage : RelatedProgramme
vikingOperatingEnvelopeLineage =
  related-programme
    "Viking Orbiter '75 beryllium INTEREGEN"
    "N2O4/MMH internally regenerative beryllium chamber; enlarged nozzle relative to Mariner 9"
    "~300 lbf class"
    "five converted engines were thermally stable during the nominal 2730-s burn but had difficulty at operating extremes; the response was to map a safe thermal-equilibrium envelope and modify selected engines with acoustic-cavity fuel injection"
    "predecessor design lineage and operating-envelope lesson, not the R-9557 test article"
    "AIAA 72-1131 / NTRS 19730028636"
    false

marinerAndPBPSLineage : RelatedProgramme
marinerAndPBPSLineage =
  related-programme
    "Minuteman III PBPS / Mariner '71 INTEREGEN lineage"
    "hot-pressed beryllium conductive/film-cooled chamber family"
    "roughly 300 lbf operational lineage; broader development from 25 to 1000 lbf reported in NASA-SP-8124"
    "R-9557 states its chamber/injector/nozzle design improvements were relative to previously tested INTEREGEN thrusters and reduced heat transfer by about 20-30 percent"
    "engineering lineage and design prior art, not identical hardware"
    "R-9557-1 p.9; NASA-SP-8124 Table VI / Sec. 2.3.1"
    false

record InteregenTradeoff : Set where
  constructor interegen-tradeoff
  field
    filmCoolingRequirementUnique : Bool
    wallThicknessMayTradeAgainstFilmFlow : Bool
    materialChoiceChangesCapabilityEnvelope : Bool
    berylliumOnlyUniversalInteregenMaterial : Bool
    designImplication : String
    sourceReference : String

interegenTradeoffReceipt : InteregenTradeoff
interegenTradeoffReceipt =
  interegen-tradeoff
    false true true false
    "wall thickness, coolant-film allocation, material and operating point are coupled coordinates; a thermal observation cannot identify a unique chamber/nozzle design"
    "NASA-SP-8124 Sec. 2.3.1.1; monolithic beryllium, copper and bimetallic INTEREGEN examples"

record ChallengeAtlas : Set where
  constructor challenge-atlas
  field
    valveContamination : ProgrammeChallenge
    injectorContamination : ProgrammeChallenge
    throttleStability : ProgrammeChallenge
    structuralQualification : ProgrammeChallenge
    maintenance : ProgrammeChallenge
    massOpportunity : ProgrammeChallenge
    repeatedValveMechanism : RepeatedValveFailure
    predecessorEnvelopeLesson : RelatedProgramme
    interegenDesignTradeoff : InteregenTradeoff
    dominant1974ObservedProblemsCoolingIntrinsic : Bool
    sourceBoundary : String

canonicalChallengeAtlas : ChallengeAtlas
canonicalChallengeAtlas =
  challenge-atlas
    sandDustValveChallenge
    orificePluggingChallenge
    lowThrottleOscillationChallenge
    brazeJointChallenge
    maintainabilityChallenge
    weightReductionOpportunity
    valveSerialFailurePair
    vikingOperatingEnvelopeLineage
    interegenTradeoffReceipt
    false
    "R-9557-1 explicitly says valve failure and injector plugging were independent of the INTEREGEN cooling process; preserve that attribution rather than calling every programme problem a beryllium/thermal failure."

record ChallengeAcquisitionFrontier : Set where
  constructor challenge-acquisition-frontier
  field
    fullValveFailureAnalysis : Bool
    particleTransportPath : Bool
    fullInjectorPluggingMap : Bool
    lowThrottleDynamicTimeSeries : Bool
    exactBrazeProcessAndLotData : Bool
    engineeringChangeOrder : Bool
    nextSource : String

challengeAcquisitionFrontier : ChallengeAcquisitionFrontier
challengeAcquisitionFrontier =
  challenge-acquisition-frontier
    true false false false false false
    "The executive summary pays the valve failure mechanism and repeated serial observations; next acquire detailed Moog/NAS9-12996 disassembly/test records, particle transport geometry, throttle dynamic records, braze process qualification and engineering-change documentation."
