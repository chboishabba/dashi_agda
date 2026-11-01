module DASHI.Law.SolomonIslandsForeignInterferenceRelayTopologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.OperationalDirectionProvenanceBidiExact as Direction
import DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact as Defeat

------------------------------------------------------------------------
-- TWO-STAGE COMMUNICATION TOPOLOGY
--
-- Current public reporting supports a materially different topology from a
-- direct Australian instruction to defeat the motion:
--
--   Australian High Commission -> Francis Sade
--      treaty/funding update + "hold steady" language
--
--   Francis Sade -> Solomon Islands coalition MP(s)
--      domestic political exhortation / defeat-motion language
--
-- The second message is not thereby Australian speech, and the first message is
-- not thereby a command governing the second.  Any shared-intent, inducement,
-- conditionality or causal bridge requires separate evidence.
------------------------------------------------------------------------

data RelayActor : Set where
  australianHighCommission : RelayActor
  francisSade : RelayActor
  coalitionMember : RelayActor

data RelayContentClass : Set where
  treatyFundingUpdate : RelayContentClass
  holdSteadyLanguage : RelayContentClass
  coalitionPoliticalExhortation : RelayContentClass
  defeatMotionLanguage : RelayContentClass

data RelaySourceStatus : Set where
  authenticatedJournalisticReport : RelaySourceStatus
  namedSecondaryReport : RelaySourceStatus
  primaryArtifactVerified : RelaySourceStatus
  unresolvedRelayStatus : RelaySourceStatus

record RelayEdge : Set where
  constructor relay-edge
  field
    sender : RelayActor
    recipient : RelayActor
    contentClass : RelayContentClass
    sourceStatus : RelaySourceStatus
    sourceReference : String
    primaryArtifactClosed : Bool

open RelayEdge public

highCommissionToSadeFundingEdge : RelayEdge
highCommissionToSadeFundingEdge = relay-edge
  australianHighCommission
  francisSade
  treatyFundingUpdate
  authenticatedJournalisticReport
  "ABC News authenticated High Commissioner Jeffrey Roach -> Deputy PM Francis Sade treaty/funding communication"
  false

highCommissionToSadeHoldSteadyEdge : RelayEdge
highCommissionToSadeHoldSteadyEdge = relay-edge
  australianHighCommission
  francisSade
  holdSteadyLanguage
  authenticatedJournalisticReport
  "ABC News reports/authenticates Roach text containing 'hold steady' language"
  false

sadeToCoalitionPoliticalEdge : RelayEdge
sadeToCoalitionPoliticalEdge = relay-edge
  francisSade
  coalitionMember
  coalitionPoliticalExhortation
  namedSecondaryReport
  "AAP reporting identifies Sade's own message as aimed at wavering coalition MPs"
  false

sadeToCoalitionDefeatMotionEdge : RelayEdge
sadeToCoalitionDefeatMotionEdge = relay-edge
  francisSade
  coalitionMember
  defeatMotionLanguage
  namedSecondaryReport
  "Opposition statement plus later reporting attribute stand-together/defeat-motion language to a subsequent Sade message"
  false

------------------------------------------------------------------------
-- Cross-pollination with OperationalDirectionProvenanceBidiExact.
--
-- That generic owner already separates issuer, content, transmission and field
-- receipt.  We reuse its central rule: existence of an upstream communication
-- does not prove that a downstream actor's action was governed by it.
------------------------------------------------------------------------

record RelayGovernanceCutset : Set where
  constructor relay-governance-cutset
  field
    upstreamCommunicationKnown : Bool
    upstreamCommunicationKnownIsTrue : upstreamCommunicationKnown ≡ true
    downstreamPoliticalMessageKnownByReport : Bool
    downstreamPoliticalMessageKnownByReportIsTrue : downstreamPoliticalMessageKnownByReport ≡ true
    forwardingBoundaryKnownByReport : Bool
    forwardingBoundaryKnownByReportIsTrue : forwardingBoundaryKnownByReport ≡ true
    australianRequestedDefeatMotion : Bool
    australianRequestedDefeatMotionIsFalse : australianRequestedDefeatMotion ≡ false
    australianConditionedBenefitsOnDefeatingMotion : Bool
    australianConditionedBenefitsOnDefeatingMotionIsFalse :
      australianConditionedBenefitsOnDefeatingMotion ≡ false
    sharedIntentEstablished : Bool
    sharedIntentEstablishedIsFalse : sharedIntentEstablished ≡ false
    causalGovernanceEstablished : Bool
    causalGovernanceEstablishedIsFalse : causalGovernanceEstablished ≡ false

open RelayGovernanceCutset public

currentRelayGovernanceCutset : RelayGovernanceCutset
currentRelayGovernanceCutset = relay-governance-cutset
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- The legal interference hinge after correction.
------------------------------------------------------------------------

data RelayInterferenceResidual : Set where
  exactThreadArtifactResidual : RelayInterferenceResidual
  conditionalityResidual : RelayInterferenceResidual
  sharedIntentResidual : RelayInterferenceResidual
  causationResidual : RelayInterferenceResidual
  relayInterferenceClosed : RelayInterferenceResidual

firstRelayResidual : RelayGovernanceCutset → RelayInterferenceResidual
firstRelayResidual c with primaryArtifactClosed highCommissionToSadeFundingEdge
... | false = exactThreadArtifactResidual
... | true with australianConditionedBenefitsOnDefeatingMotion c
...   | false = conditionalityResidual
...   | true with sharedIntentEstablished c
...     | false = sharedIntentResidual
...     | true with causalGovernanceEstablished c
...       | false = causationResidual
...       | true = relayInterferenceClosed

currentFirstRelayResidual :
  firstRelayResidual currentRelayGovernanceCutset ≡ exactThreadArtifactResidual
currentFirstRelayResidual = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ForwardingTransfersAuthorship : Set where
data TemporalSequenceEstablishesInstruction : Set where
data BenefitAnnouncementEstablishesConditionality : Set where
data DomesticPoliticalUseEstablishesForeignIntent : Set where

forwardingDoesNotTransferAuthorship : ForwardingTransfersAuthorship → ⊥
forwardingDoesNotTransferAuthorship ()

temporalSequenceDoesNotEstablishInstruction :
  TemporalSequenceEstablishesInstruction → ⊥
temporalSequenceDoesNotEstablishInstruction ()

benefitsDoNotAutoEstablishConditionality :
  BenefitAnnouncementEstablishesConditionality → ⊥
benefitsDoNotAutoEstablishConditionality ()

domesticUseDoesNotAutoEstablishForeignIntent :
  DomesticPoliticalUseEstablishesForeignIntent → ⊥
domesticUseDoesNotAutoEstablishForeignIntent ()

------------------------------------------------------------------------
-- Current acquisition statement.
------------------------------------------------------------------------

currentRelayAcquisition : String
currentRelayAcquisition =
  "Acquire the original WhatsApp chain or independently authenticated screenshots/exports showing forwarding markers, sender/recipient identities and timestamps; then test whether any Australian message conditioned funding/treaty benefits on government survival or requested use of the package to defeat the no-confidence motion"
