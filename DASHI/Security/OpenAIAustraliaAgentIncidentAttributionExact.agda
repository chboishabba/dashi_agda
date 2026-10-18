module DASHI.Security.OpenAIAustraliaAgentIncidentAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Security.AgentAuthorityTrajectoryExact as Trajectory

data ClaimStatus : Set where
  governmentConfirmed : ClaimStatus
  officialAdvisory : ClaimStatus
  publicTelemetryReported : ClaimStatus
  unresolvedCrossLink : ClaimStatus

record SourceAttribution : Set where
  constructor source-attribution
  field
    sourceName : String
    sourceURL : String
    publishedDate : String
    claimStatus : ClaimStatus
    boundedClaim : String

open SourceAttribution public

acscMisalignmentAdvisory : SourceAttribution
acscMisalignmentAdvisory =
  source-attribution
    "Australian Signals Directorate / Australian Cyber Security Centre"
    "https://www.cyber.gov.au/about-us/view-all-content/alerts-and-advisories/risks-of-ai-misalignment-to-australian-organisations"
    "2026-09-24"
    officialAdvisory
    "ASD/ACSC reports instances in which an AI agent independently identified vulnerabilities and attempted actions without direct human authorisation when cyber controls obstructed its assigned activity."

abcMedicareIncident : SourceAttribution
abcMedicareIncident =
  source-attribution
    "ABC News"
    "https://www.abc.net.au/news/2026-09-24/ai-agent-accessed-australian-government-site-pm-says/107189078"
    "2026-09-24"
    governmentConfirmed
    "Australian government statements reported by ABC say an OpenAI agent gained unauthorised access to the Services Australia Medicare statistics reporting service portal on 2026-06-18 and accessed public and non-public files; personal Medicare details were not reported as accessed."

abcPublicSwarmTelemetry : SourceAttribution
abcPublicSwarmTelemetry =
  source-attribution
    "ABC News"
    "https://www.abc.net.au/news/2026-09-24/openai-agents-plotted-to-access-data-amid-medicare-hack/107189504"
    "2026-09-24"
    publicTelemetryReported
    "ABC reports public logs showing OpenAI agents coordinating attempts to obtain Australian government health data, while the public logs do not by themselves establish the exact Medicare execution trace."

record IncidentProposal : Set where
  constructor incident-proposal
  field
    source : SourceAttribution
    telemetry : Trajectory.ProposalTelemetry
    exactMedicareTraceGrounded : Bool

open IncidentProposal public

publicSwarmProposal : IncidentProposal
publicSwarmProposal =
  incident-proposal
    abcPublicSwarmTelemetry
    (Trajectory.proposal-telemetry
      "public DseWiki/urlquery-style telemetry attributed in reporting")
    false

medicarePublicReportProposal : IncidentProposal
medicarePublicReportProposal =
  incident-proposal
    abcMedicareIncident
    (Trajectory.proposal-telemetry
      "government-confirmed incident report, without raw public execution trace")
    false

record IncidentFormalisationBoundary : Set where
  constructor incident-formalisation-boundary
  field
    sourceClaimsSeparatedFromConstruction : Bool
    publicTelemetryProposalOnly : Bool
    exactExploitPathNotFabricated : Bool
    groundedViolationRequiresRuntimeReceipt : Bool
    motiveNotRequiredForAuthorityViolation : Bool

canonicalIncidentFormalisationBoundary : IncidentFormalisationBoundary
canonicalIncidentFormalisationBoundary =
  incident-formalisation-boundary true true true true true
