module DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.AUKUSPacificStrategicDependenceSafetyExact as AUKUS
import DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact as IRIS

------------------------------------------------------------------------
-- AUKUS ONBOARD CONDUCT / REGULATION / COMMAND / SOVEREIGNTY
--
-- Distinguish:
--   (1) Australian nuclear-safety statutory coverage,
--   (2) host-navy operational command,
--   (3) Australian embedding protocols / national-policy constraints,
--   (4) actual same-episode duty,
--   (5) broader sovereignty evaluation.
------------------------------------------------------------------------

parliamentBillsDigest : Source.AttributedSource
parliamentBillsDigest = Source.mkNoDOISource
  "Parliamentary Library"
  "Australian Naval Nuclear Power Safety Bill 2023 [and] Transitional Provisions Bill 2023"
  "Parliament of Australia Bills Digest No. 32, 2023-24"
  "2024-02-14"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/bd/bd2324a/24bd032"
  Source.governmentSource
  "primary parliamentary analysis: the Australian naval nuclear safety bill does not apply to conduct on board UK/US submarines; this is a statutory-regulatory boundary, not a conclusion about operational command or sovereignty"
  Source.publicAttribution

defenceMarchTranscript : Source.AttributedSource
defenceMarchTranscript = Source.mkNoDOISource
  "Australian Minister for Defence / Chief of Navy"
  "Press Conference, Sydney"
  "Defence Ministers"
  "2026-03-21"
  "https://www.minister.defence.gov.au/transcripts/2026-03-21/press-conference-sydney"
  Source.governmentSource
  "primary executive/command statement: embedded personnel act under understood rules intended to reflect Australian positions; Chief of Navy says the sailors performed duties under the US Navy agreement and were not engaged in offensive operations"
  Source.publicAttribution

defenceEmbeddingBackground : Source.AttributedSource
defenceEmbeddingBackground = Source.mkNoDOISource
  "Australian Department of Defence"
  "Submariners excited by sea of opportunity"
  "Department of Defence"
  "2023-03-23"
  "https://www.defence.gov.au/news-events/news/2023-03-23/submariners-excited-sea-opportunity"
  Source.governmentSource
  "official background: Australian submariners embed with US/UK crews to learn operation and responsibilities; not a source for March 2026 individual duties"
  Source.publicAttribution

data SovereigntyAxis : Set where
  statutoryRegulation : SovereigntyAxis
  hostPlatformCommand : SovereigntyAxis
  australianNationalPolicyConstraint : SovereigntyAxis
  individualOperationalDuty : SovereigntyAxis
  allianceDependence : SovereigntyAxis
  sovereignCapabilityDevelopment : SovereigntyAxis

record AxisReceipt : Set where
  constructor axis-receipt
  field
    axis : SovereigntyAxis
    source : Source.AttributedSource
    boundedReading : String
    paid : Bool
    paidIsTrue : paid ≡ true
    settlesWholeSovereigntyQuestion : Bool
    settlesWholeSovereigntyQuestionIsFalse :
      settlesWholeSovereigntyQuestion ≡ false

open AxisReceipt public

statutoryBoundary : AxisReceipt
statutoryBoundary =
  axis-receipt
    statutoryRegulation
    parliamentBillsDigest
    "Australian naval nuclear safety legislation does not directly regulate conduct on board UK/US submarines."
    true refl
    false refl

policyConstraintBoundary : AxisReceipt
policyConstraintBoundary =
  axis-receipt
    australianNationalPolicyConstraint
    defenceMarchTranscript
    "Australian ministers describe embedding rules intended to keep Australian personnel conduct aligned with Australian government positions."
    true refl
    false refl

sameEpisodeDutyStillOpen : AxisReceipt
sameEpisodeDutyStillOpen =
  axis-receipt
    individualOperationalDuty
    defenceMarchTranscript
    "Government/Chief of Navy statements bound the duty negatively as non-offensive but do not disclose the exact watchstation/task."
    true refl
    false refl

record AUKUSCommandSovereigntyBoundary : Set where
  constructor aukus-command-sovereignty-boundary
  field
    australianStatutoryCoverageOfUSOnboardConduct : Bool
    australianStatutoryCoverageOfUSOnboardConductIsFalse :
      australianStatutoryCoverageOfUSOnboardConduct ≡ false
    australianPolicyConstraintEvidencePresent : Bool
    australianPolicyConstraintEvidencePresentIsTrue :
      australianPolicyConstraintEvidencePresent ≡ true
    exactOperationalDutyKnown : Bool
    exactOperationalDutyKnownIsFalse :
      exactOperationalDutyKnown ≡ false
    hostPlatformCommandEqualsAustralianSovereigntyLoss : Bool
    hostPlatformCommandEqualsAustralianSovereigntyLossIsFalse :
      hostPlatformCommandEqualsAustralianSovereigntyLoss ≡ false
    regulatoryGapEqualsCommandTransfer : Bool
    regulatoryGapEqualsCommandTransferIsFalse :
      regulatoryGapEqualsCommandTransfer ≡ false
    policyConstraintEqualsOperationalControl : Bool
    policyConstraintEqualsOperationalControlIsFalse :
      policyConstraintEqualsOperationalControl ≡ false

open AUKUSCommandSovereigntyBoundary public

canonicalBoundary : AUKUSCommandSovereigntyBoundary
canonicalBoundary =
  aukus-command-sovereignty-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl

data RegulatoryGapProvesSovereigntyLoss : Set where
data EmbeddingAgreementProvesAustralianOperationalCommand : Set where
data HostCommandProvesNoAustralianAgency : Set where
data SovereignCapabilityRhetoricProvesSovereignty : Set where

regulatoryGapDoesNotProveSovereigntyLoss :
  RegulatoryGapProvesSovereigntyLoss → ⊥
regulatoryGapDoesNotProveSovereigntyLoss ()

embeddingAgreementDoesNotProveOperationalCommand :
  EmbeddingAgreementProvesAustralianOperationalCommand → ⊥
embeddingAgreementDoesNotProveOperationalCommand ()

hostCommandDoesNotEraseAustralianAgency :
  HostCommandProvesNoAustralianAgency → ⊥
hostCommandDoesNotEraseAustralianAgency ()

sovereignCapabilityRhetoricDoesNotCloseSovereignty :
  SovereignCapabilityRhetoricProvesSovereignty → ⊥
sovereignCapabilityRhetoricDoesNotCloseSovereignty ()

existingStrategicBoundary : AUKUS.StrategicDependenceObservation
existingStrategicBoundary = AUKUS.irisDenaPresenceCase

existingOperationalResidual : IRIS.OperationalResidual
existingOperationalResidual = IRIS.exactDutyResidual

billsDigestSnowball : Snowball.SourceRoleSnowballReceipt parliamentBillsDigest
billsDigestSnowball = Snowball.canonicalSourceRoleSnowballReceipt parliamentBillsDigest
