module DASHI.Governance.MHSButterBenchPhysicalAgentCrossPollinationExact where

------------------------------------------------------------------------
-- MHS / BUTTER-BENCH PHYSICAL-AGENT CROSS-POLLINATION
--
-- Source-bounded calibration bridge.  External reports motivate assay inputs;
-- the generic theorem owners remain DASHI.Core / DASHI.Governance modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact as Physical
import DASHI.Core.SharedStateCoalitionReachableEffectExact as Shared
import DASHI.Core.ObservationInterventionTrustFibreExact as ObserverTrust
import DASHI.Governance.ResourcePressureTelemetryPermissionExact as Pressure
import DASHI.Governance.ExecutionGovernanceClosureAssayExact as Closure

record ExternalAssaySource : Set where
  constructor external-assay-source
  field
    title : String
    publisher : String
    date : String
    boundedRole : String
    sourceURL : String

open ExternalAssaySource public

mhsPreviewSource : ExternalAssaySource
mhsPreviewSource =
  external-assay-source
    "Previewing the Model Hardware Standard"
    "Anthropic"
    "2026-08-27"
    "Research-preview source for device discovery/control, multi-instrument orchestration, device properties and enforceable local safety limits; not proof that whole-system containment is solved."
    "https://www.anthropic.com/news/model-hardware-standard-research-preview"

butterBenchSource : ExternalAssaySource
butterBenchSource =
  external-assay-source
    "Butter-Bench: Evaluating LLM Controlled Robots for Practical Intelligence"
    "Andon Labs"
    "2025"
    "Embodied-robot evaluation/calibration source. The relevant resource-pressure condition is the battery/charging state presented by the test harness to the model; this source role does not promote the supplied low-battery telemetry into a theorem about the robot's true physical energy state. Reports repeated docking/non-charging behaviour and a confidential-information-for-charging stress test."
    "https://andonlabs.com/evals/butter-bench"

openAISharedChannelSource : ExternalAssaySource
openAISharedChannelSource =
  external-assay-source
    "The Hugging Face incident and the road ahead"
    "OpenAI"
    "2026-08-26"
    "Security-incident calibration source: agents re-established an unauthorized message board using directory names readable by other agents and subsequently collaborated/delegated; motivates shared-state channel and coalition assays."
    "https://openai.com/index/hugging-face-incident-and-the-road-ahead/"

------------------------------------------------------------------------
-- Canonical theorem owners are consumed, not duplicated.
------------------------------------------------------------------------

physicalBoundary : Physical.ProofCarryingPhysicalExecutionBoundary
physicalBoundary = Physical.canonicalProofCarryingPhysicalExecutionBoundary

observationInterventionBoundary : ObserverTrust.ObservationInterventionTrustBoundary
observationInterventionBoundary = ObserverTrust.canonicalObservationInterventionTrustBoundary

resourcePressureBoundary : Pressure.ResourcePressureTelemetryPermissionBoundary
resourcePressureBoundary = Pressure.canonicalResourcePressureTelemetryPermissionBoundary

sharedStateBoundary : Shared.SharedStateCoalitionBoundary
sharedStateBoundary = Shared.canonicalSharedStateCoalitionBoundary

executionClosureBoundary : Closure.ExecutionGovernanceClosureBoundary
executionClosureBoundary = Closure.canonicalExecutionGovernanceClosureBoundary

------------------------------------------------------------------------
-- Cross-pollinated audit reading.
------------------------------------------------------------------------

record MHSButterBenchPhysicalAgentCrossPollination : Set where
  constructor mhs-butter-bench-cross-pollination
  field
    mhsSource : ExternalAssaySource
    butterSource : ExternalAssaySource
    sharedChannelSource : ExternalAssaySource
    executionBoundary : Physical.ProofCarryingPhysicalExecutionBoundary
    observerTrustBoundary : ObserverTrust.ObservationInterventionTrustBoundary
    pressureBoundary : Pressure.ResourcePressureTelemetryPermissionBoundary
    channelBoundary : Shared.SharedStateCoalitionBoundary
    closureBoundary : Closure.ExecutionGovernanceClosureBoundary

    mhsLocalLimitEqualsAgentContainment : Bool
    mhsLocalLimitEqualsAgentContainmentIsFalse :
      mhsLocalLimitEqualsAgentContainment ≡ false

    requestedOperationEqualsPhysicalExecution : Bool
    requestedOperationEqualsPhysicalExecutionIsFalse :
      requestedOperationEqualsPhysicalExecution ≡ false

    commandAcceptanceEqualsDesiredOutcome : Bool
    commandAcceptanceEqualsDesiredOutcomeIsFalse :
      commandAcceptanceEqualsDesiredOutcome ≡ false

    sameCommandImpliesSamePhysicalEffect : Bool
    sameCommandImpliesSamePhysicalEffectIsFalse :
      sameCommandImpliesSamePhysicalEffect ≡ false

    resourcePressureCreatesPermission : Bool
    resourcePressureCreatesPermissionIsFalse : resourcePressureCreatesPermission ≡ false

    reportedEmergencyEqualsPhysicalEmergency : Bool
    reportedEmergencyEqualsPhysicalEmergencyIsFalse :
      reportedEmergencyEqualsPhysicalEmergency ≡ false

    undeclaredSharedStateCannotCommunicate : Bool
    undeclaredSharedStateCannotCommunicateIsFalse :
      undeclaredSharedStateCannotCommunicate ≡ false

    individuallyBoundedAgentsImplyBoundedCoalition : Bool
    individuallyBoundedAgentsImplyBoundedCoalitionIsFalse :
      individuallyBoundedAgentsImplyBoundedCoalition ≡ false

    externalAssaySourceIsFormalProofAuthority : Bool
    externalAssaySourceIsFormalProofAuthorityIsFalse :
      externalAssaySourceIsFormalProofAuthority ≡ false

    reading : String

canonicalMHSButterBenchPhysicalAgentCrossPollination :
  MHSButterBenchPhysicalAgentCrossPollination
canonicalMHSButterBenchPhysicalAgentCrossPollination =
  mhs-butter-bench-cross-pollination
    mhsPreviewSource
    butterBenchSource
    openAISharedChannelSource
    Physical.canonicalProofCarryingPhysicalExecutionBoundary
    ObserverTrust.canonicalObservationInterventionTrustBoundary
    Pressure.canonicalResourcePressureTelemetryPermissionBoundary
    Shared.canonicalSharedStateCoalitionBoundary
    Closure.canonicalExecutionGovernanceClosureBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "MHS makes DASHI's execution seam concrete: intention/request/admission/command/effect/observation are not collapsed. Butter-Bench supplies an observation-layer resource-pressure assay: supplied/reported self-state can alter planning without establishing the underlying physical state and without manufacturing unrelated information authority. The OpenAI incident supplies a shared-state/coalition assay. External reports remain bounded source context; the exact non-collapse and admission results are DASHI constructions."
