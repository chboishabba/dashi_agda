module DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- FISSION SURFACE POWER INSTRUMENTATION & CONTROLS SCIENCE
--
-- The public NASA material is a technology-maturation architecture rather than
-- one device equation.  The scientific/engineering carrier is a closed sensing,
-- estimation, protection and actuation loop operating under space-nuclear
-- environmental and reliability constraints.
------------------------------------------------------------------------

data ICFunction : Set where
  sense
  conditionSignal
  estimateState
  compareToRequirement
  commandActuator
  protectSystem
  recordTelemetry
  diagnoseFault
  : ICFunction

data ICRiskAxis : Set where
  radiation
  temperature
  lifetime
  reliability
  qualification
  sensorDrift
  electronicsDegradation
  communication
  : ICRiskAxis

record ICChain : Set where
  constructor ic-chain
  field
    stages : List ICFunction
    sourceReference : String
    boundedReading : String

canonicalICChain : ICChain
canonicalICChain = ic-chain
  ( sense
  ∷ conditionSignal
  ∷ estimateState
  ∷ compareToRequirement
  ∷ commandActuator
  ∷ protectSystem
  ∷ recordTelemetry
  ∷ diagnoseFault
  ∷ [] )
  "NASA NTRS 20250008475 and 2024 Fission Instrumentation & Controls Workshop outputs"
  "This is a typed engineering abstraction of the I&C function family, not a claim that every FSP subsystem uses this exact serial implementation."

ficsDatabaseRole : S.ScientificMechanismReceipt
ficsDatabaseRole = S.scientific-mechanism-receipt
  "Fission Instrumentation & Controls technology maturation"
  "a live FICS/CINDI database is used to capture technologies, gaps, readiness and development information supporting the FSP/SNP I&C maturation path"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "NASA NTRS 20250008475"
  "The database is an engineering knowledge/decision support object; this receipt does not establish its public access status or that it contains complete design data."

workingGroupRole : S.ScientificMechanismReceipt
workingGroupRole = S.scientific-mechanism-receipt
  "Fission Instrumentation & Controls Working Group"
  "the working group coordinates cross-cutting maturation of fission I&C technology and feeds a draft technology growth path"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "NASA NTRS 20250008475"
  "Organisational coordination is part of the technology-maturation architecture but does not itself prove readiness of any component."

technologyGrowthPath : S.ScientificMechanismReceipt
technologyGrowthPath = S.scientific-mechanism-receipt
  "40 kW Fission Surface Power I&C"
  "technology maturation is organised as a path from identified gaps and candidate technologies toward increasingly qualified, integrated and mission-ready I&C capability"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "NASA NTRS 20250008475"
  "The public presentation describes the path and programme outputs; exact qualification evidence remains component- and test-specific."

icNeedsQualificationReceipts : S.ScientificReverseObligation
icNeedsQualificationReceipts = S.scientific-reverse-obligation
  "FSP/SNP I&C component readiness"
  S.benchmarkReceipt
  "recover component-specific radiation, temperature, lifetime, reliability, drift, fault-tolerance and integrated-environment qualification tests"
  "whether a particular sensor/electronics/control technology satisfies its mission environment and reliability requirements"
  "flight readiness merely from inclusion in the technology database or growth path"

record CurrentLeBlancICScienceAssessment : Set where
  constructor current-leblanc-ic-science-assessment
  field
    controlArchitectureOwned : Bool
    controlArchitectureOwnedIsTrue : controlArchitectureOwned ≡ true
    databaseAndWorkingGroupOwned : Bool
    databaseAndWorkingGroupOwnedIsTrue : databaseAndWorkingGroupOwned ≡ true
    componentQualificationClosed : Bool
    componentQualificationClosedIsFalse : componentQualificationClosed ≡ false

canonicalCurrentLeBlancICScienceAssessment : CurrentLeBlancICScienceAssessment
canonicalCurrentLeBlancICScienceAssessment = current-leblanc-ic-science-assessment
  true refl
  true refl
  false refl
