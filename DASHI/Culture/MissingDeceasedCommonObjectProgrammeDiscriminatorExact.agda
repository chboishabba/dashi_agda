module DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as Science
import DASHI.Culture.MissingDeceasedUAPAdversarialClaimDiscriminatorExact as UAP
import DASHI.Culture.MissingDeceasedSouthwestGeographyDiscriminatorExact as Geography

------------------------------------------------------------------------
-- OBJECT-FIRST COMMON-PROGRAMME / COMMON-CAUSE DISCRIMINATOR
--
-- This owner does not start from an assumed common cause.  It asks whether a
-- literal programme/object explains source-backed capabilities and chronology
-- better than independent events, broad strategic-sector exposure, or ordinary
-- programme succession.  H3 is deliberately gated by operational evidence.
------------------------------------------------------------------------

data HypothesisClass : Set where
  H0 H1 H2 H3 : HypothesisClass

data ProgrammeClass : Set where
  longDurationAutonomousExtremeEnvironment : ProgrammeClass
  highEnergyExperimentalInfrastructure : ProgrammeClass
  advancedPropulsionAnomalousFieldTestbed : ProgrammeClass
  strategicRDPortfolio : ProgrammeClass

data EventClass : Set where
  disappearance : EventClass
  death : EventClass
  homicide : EventClass
  accident : EventClass
  illness : EventClass
  retirementOrSeparation : EventClass
  staleInstitutionalSurface : EventClass
  posthumousPublication : EventClass
  ordinaryRoleTransition : EventClass

data ReceiptStrength : Set where
  capabilityOnly : ReceiptStrength
  thematicAdjacency : ReceiptStrength
  literalSameObject : ReceiptStrength
  literalCrossPerson : ReceiptStrength
  operationalTargeting : ReceiptStrength

record RequiredCapability : Set where
  constructor required-capability
  field
    capabilityName : String
    scienceOwner : String
    whyRequired : String

open RequiredCapability public

record CandidateObject : Set where
  constructor candidate-object
  field
    objectName : String
    objectClass : ProgrammeClass
    requirements : List RequiredCapability
    explainedCapabilityCount : Nat
    literalCrossPersonReceiptCount : Nat
    inventedInterfaceCount : Nat
    eventAlignmentCount : Nat
    alternativeExplanationDebt : Nat
    targetingEvidenceCount : Nat

open CandidateObject public

record CandidateProgramme : Set where
  constructor candidate-programme
  field
    programmeName : String
    programmeClass : ProgrammeClass
    objects : List CandidateObject
    currentPromotion : HypothesisClass
    literalProgrammeIdentityPaid : Bool
    coordinatedTargetingPaid : Bool

open CandidateProgramme public

record PersonCapabilityReceipt : Set where
  constructor person-capability-receipt
  field
    person : String
    candidateObject : String
    capability : String
    sourceBackedScience : String
    receiptStrength : ReceiptStrength
    sameObjectMembershipPaid : Bool

open PersonCapabilityReceipt public

record CrossPersonProgrammeReceipt : Set where
  constructor cross-person-programme-receipt
  field
    candidateProgramme : String
    participantA : String
    participantB : String
    sharedObjectOrIdentifier : String
    sourceReference : String
    strength : ReceiptStrength
    literalCrossPersonPaid : Bool
    whatItCannotPay : String

open CrossPersonProgrammeReceipt public

record EventChronologyReceipt : Set where
  constructor event-chronology-receipt
  field
    person : String
    eventClass : EventClass
    eventDateOrRange : String
    sourceReference : String
    publicationLagRelevant : Bool
    eventIdentityPaid : Bool
    causeOrMannerPaid : Bool

open EventChronologyReceipt public

record HypothesisDiscriminationReceipt : Set where
  constructor hypothesis-discrimination-receipt
  field
    candidate : String
    hypothesis : HypothesisClass
    capabilityFitCount : Nat
    literalCrossPersonCount : Nat
    operationalEvidenceCount : Nat
    alternativeExplanation : String
    currentStatus : String
    promoted : Bool

open HypothesisDiscriminationReceipt public

------------------------------------------------------------------------
-- Initial object classes: capability consumers only, not historical systems.
------------------------------------------------------------------------

longDurationRequirements : List RequiredCapability
longDurationRequirements =
  required-capability "plasma/environment modelling" "Loureiro KREHM/Viriato owners" "model plasma and magnetised environment" ∷
  required-capability "fission power instrumentation/control" "LeBlanc FSP I&C owners" "long-duration harsh-environment power/control" ∷
  required-capability "extreme-environment materials" "Reza/Zhou/Fang material owners" "survive oxygen, thermal and structural loads" ∷
  required-capability "fault-tolerant sensing/control" "McCasland Gramian owner" "retain controllability/observability under failures" ∷
  required-capability "autonomy" "Zhang Daibing control owner" "remote guidance and control" ∷
  required-capability "space-weather risk" "Zhang Xiaoxin forecast owner" "environmental hazard prediction" ∷ []

longDurationObject : CandidateObject
longDurationObject = candidate-object
  "long-duration autonomous extreme-environment aerospace/space platform"
  longDurationAutonomousExtremeEnvironment
  longDurationRequirements
  12 0 5 0 4 0

highEnergyRequirements : List RequiredCapability
highEnergyRequirements =
  required-capability "accelerator/radiographic diagnostics" "Chavez DARHT/Scorpius owner" "high-energy diagnostic source and accelerator engineering" ∷
  required-capability "controls and qualification" "LeBlanc/McCasland owners" "instrumentation, sensing and fault tolerance" ∷
  required-capability "materials" "Reza/Zhou/Fang owners" "survive high-energy/extreme environments" ∷
  required-capability "molecular diagnostics" "Maiwald spectroscopy owner" "identify molecular species in controlled experiments" ∷
  required-capability "precision-force discrimination" "Ning/Amy mechanism-discrimination owners" "test anomalous-force hypotheses under controls" ∷ []

highEnergyObject : CandidateObject
highEnergyObject = candidate-object
  "high-energy experimental/test infrastructure"
  highEnergyExperimentalInfrastructure
  highEnergyRequirements
  10 0 4 0 4 0

advancedPropulsionRequirements : List RequiredCapability
advancedPropulsionRequirements =
  required-capability "superconducting-gravity experimental constraints" "Ning Li owners" "bound/test superconducting-gravity mechanisms" ∷
  required-capability "engineered-gravity mechanism discrimination" "Amy Eskridge owners" "separate mechanism claims from controls/confounders" ∷
  required-capability "plasma dynamics" "Loureiro owners" "model magnetised plasma/reconnection regimes" ∷
  required-capability "materials and structures" "Reza/Fang owners" "supply bounded high-performance material/structure interfaces" ∷
  required-capability "instrumentation and fault tolerance" "LeBlanc/McCasland owners" "measure/control a difficult experimental platform" ∷ []

advancedPropulsionObject : CandidateObject
advancedPropulsionObject = candidate-object
  "advanced propulsion / anomalous-field research testbed"
  advancedPropulsionAnomalousFieldTestbed
  advancedPropulsionRequirements
  7 0 6 0 6 0

portfolioObject : CandidateObject
portfolioObject = candidate-object
  "multi-object strategic R&D portfolio"
  strategicRDPortfolio
  (required-capability "multiple domain-specialist objects" "twenty-scientist science capability BIDI" "allow multiple objects without forcing a single-machine identity" ∷ [])
  20 0 0 0 5 0

longDurationProgramme : CandidateProgramme
longDurationProgramme = candidate-programme
  "ordinary long-duration autonomous extreme-environment programme candidate"
  longDurationAutonomousExtremeEnvironment
  (longDurationObject ∷ [])
  H1 false false

highEnergyProgramme : CandidateProgramme
highEnergyProgramme = candidate-programme
  "high-energy experimental infrastructure candidate"
  highEnergyExperimentalInfrastructure
  (highEnergyObject ∷ [])
  H1 false false

advancedPropulsionProgramme : CandidateProgramme
advancedPropulsionProgramme = candidate-programme
  "advanced propulsion/anomalous-field testbed candidate"
  advancedPropulsionAnomalousFieldTestbed
  (advancedPropulsionObject ∷ [])
  H1 false false

strategicPortfolioProgramme : CandidateProgramme
strategicPortfolioProgramme = candidate-programme
  "strategic multi-object R&D portfolio candidate"
  strategicRDPortfolio
  (portfolioObject ∷ [])
  H1 false false

initialCandidateProgrammes : List CandidateProgramme
initialCandidateProgrammes =
  longDurationProgramme ∷ highEnergyProgramme ∷ advancedPropulsionProgramme ∷ strategicPortfolioProgramme ∷ []

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

capabilityFitPaysProgrammeIdentity : Bool
capabilityFitPaysProgrammeIdentity = false

temporalClusterPaysCoordination : Bool
temporalClusterPaysCoordination = false

programmeIdentityPaysTargeting : Bool
programmeIdentityPaysTargeting = false

geographyPaysCommonCause : Bool
geographyPaysCommonCause = false

technicalAdjacencyPaysCommonProgramme : Bool
technicalAdjacencyPaysCommonProgramme = false

commonObjectRequiresLiteralCrossPersonReceipt : Bool
commonObjectRequiresLiteralCrossPersonReceipt = true

coordinatedTargetingRequiresOperationalEvidence : Bool
coordinatedTargetingRequiresOperationalEvidence = true

portfolioObjectMembershipRequiresSameObjectReceipt : Bool
portfolioObjectMembershipRequiresSameObjectReceipt = true

sourceRepetitionPaysIndependentCorroboration : Bool
sourceRepetitionPaysIndependentCorroboration = false

existingEngineeringStackBoundary : Bool
existingEngineeringStackBoundary = UAP.technicalAdjacencyDoesNotCreateEngineeringStack

existingGeographyBoundary : Bool
existingGeographyBoundary = Geography.geographyDoesNotCreateCommonCause

scienceCapabilitySurfaceAvailable : Bool
scienceCapabilitySurfaceAvailable = true
