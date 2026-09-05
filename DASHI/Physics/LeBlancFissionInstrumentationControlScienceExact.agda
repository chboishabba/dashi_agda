module DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

data ICFunction : Set where sense conditionSignal estimateState compareToRequirement commandActuator protectSystem recordTelemetry diagnoseFault : ICFunction
data ICRiskAxis : Set where radiation temperature lifetime reliability qualification sensorDrift electronicsDegradation communication : ICRiskAxis
record ICChain : Set where constructor ic-chain; field stages : List ICFunction; sourceReference : String; boundedReading : String
open ICChain public
canonicalICChain = ic-chain (sense ∷ conditionSignal ∷ estimateState ∷ compareToRequirement ∷ commandActuator ∷ protectSystem ∷ recordTelemetry ∷ diagnoseFault ∷ []) "NASA NTRS 20250008475 and 2024 Fission Instrumentation & Controls Workshop outputs" "Typed engineering abstraction of the I&C function family, not a claim that every subsystem uses this exact serial implementation."

ficsDatabaseRole : S.ScientificMechanismReceipt
ficsDatabaseRole = S.scientific-mechanism-receipt "Fission Instrumentation & Controls technology maturation" "a live FICS/CINDI database captures technologies, gaps, readiness and development information supporting the FSP/SNP I&C maturation path" S.constitutiveOrEngineeringMechanism S.sourceBacked "NASA NTRS 20250008475" "The database is an engineering knowledge/decision-support object; this does not establish its public access status or complete design-data coverage."
workingGroupRole : S.ScientificMechanismReceipt
workingGroupRole = S.scientific-mechanism-receipt "Fission Instrumentation & Controls Working Group" "the working group coordinates cross-cutting maturation and feeds a draft technology growth path" S.constitutiveOrEngineeringMechanism S.sourceBacked "NASA NTRS 20250008475" "Coordination does not itself prove readiness of any component."
technologyGrowthPath : S.ScientificMechanismReceipt
technologyGrowthPath = S.scientific-mechanism-receipt "40 kW Fission Surface Power I&C" "maturation proceeds from identified gaps/candidate technologies toward increasingly qualified, integrated and mission-ready I&C capability" S.constitutiveOrEngineeringMechanism S.sourceBacked "NASA NTRS 20250008475" "Exact qualification remains component- and test-specific."
icNeedsQualificationReceipts : S.ScientificReverseObligation
icNeedsQualificationReceipts = S.scientific-reverse-obligation "FSP/SNP I&C component readiness" S.benchmarkReceipt "recover component-specific radiation, temperature, lifetime, reliability, drift, fault-tolerance and integrated-environment qualification tests" "whether a particular technology satisfies mission environment/reliability requirements" "flight readiness merely from inclusion in the database or growth path"
record CurrentLeBlancICScienceAssessment : Set where constructor current-leblanc-ic-science-assessment; field controlArchitectureOwned : Bool; controlArchitectureOwnedIsTrue : controlArchitectureOwned ≡ true; databaseAndWorkingGroupOwned : Bool; databaseAndWorkingGroupOwnedIsTrue : databaseAndWorkingGroupOwned ≡ true; componentQualificationClosed : Bool; componentQualificationClosedIsFalse : componentQualificationClosed ≡ false
canonicalCurrentLeBlancICScienceAssessment = current-leblanc-ic-science-assessment true refl true refl false refl
