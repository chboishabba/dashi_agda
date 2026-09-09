module DASHI.Law.SensibLawWoogarooPoliticalAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact as Decision

------------------------------------------------------------------------
-- WOOGAROO POLITICAL ALIGNMENT / ADVOCACY ROUTING
--
-- Party and government/opposition status can affect advocacy routing and
-- coordination incentives. They do not create statutory decision power,
-- evidentiary sufficiency, legal applicability, or an approval/refusal outcome.
------------------------------------------------------------------------

data PartyAffiliation : Set where
  australianLaborParty : PartyAffiliation
  liberalNationalPartyQueensland : PartyAffiliation
  nonPartisanPublicServiceRole : PartyAffiliation
  partyNotAttributedHere : PartyAffiliation

data GovernmentPosition : Set where
  commonwealthGovernment : GovernmentPosition
  queenslandGovernment : GovernmentPosition
  queenslandOpposition : GovernmentPosition
  parliamentaryOfficeNoExecutiveInference : GovernmentPosition
  publicServiceDelegatePosition : GovernmentPosition

data AdvocacyLeverage : Set where
  statutoryDecisionConsumer : AdvocacyLeverage
  portfolioEscalationRoute : AdvocacyLeverage
  electorateRepresentationRoute : AdvocacyLeverage
  stateProtectionMinisterRoute : AdvocacyLeverage

record PoliticalAlignmentReceipt : Set where
  constructor political-alignment-receipt
  field
    person : Decision.PersonRef
    party : PartyAffiliation
    governmentPosition : GovernmentPosition
    advocacyLeverage : AdvocacyLeverage
    boundedProposition : String
    primaryOrOfficialSource : String
    sourcePaid : Bool

open PoliticalAlignmentReceipt public

declanOConnorCoxAlignment : PoliticalAlignmentReceipt
declanOConnorCoxAlignment = political-alignment-receipt
  Decision.declanOConnorCox
  nonPartisanPublicServiceRole
  publicServiceDelegatePosition
  statutoryDecisionConsumer
  "For EPBC 2019/8575, Declan O'Connor-Cox is carried as the authorised public-service delegate; no party-political affiliation is attributed by this owner."
  "National Environmental Protection Agency s 130(1A) extension notice dated 2 September 2026"
  true

murrayWattAlignment : PoliticalAlignmentReceipt
murrayWattAlignment = political-alignment-receipt
  Decision.murrayWatt
  australianLaborParty
  commonwealthGovernment
  portfolioEscalationRoute
  "Murray Watt is an Australian Labor Party senator and Commonwealth Minister for the Environment and Water."
  "Parliament of Australia parliamentarian profile; DCCEEW Ministers website"
  true

miltonDickAlignment : PoliticalAlignmentReceipt
miltonDickAlignment = political-alignment-receipt
  Decision.miltonDick
  australianLaborParty
  parliamentaryOfficeNoExecutiveInference
  electorateRepresentationRoute
  "Milton Dick is the Australian Labor Party Member for Oxley and Speaker; party/electorate representation does not confer EPBC approval power."
  "Parliament of Australia parliamentarian profile"
  true

shayneNeumannAlignment : PoliticalAlignmentReceipt
shayneNeumannAlignment = political-alignment-receipt
  Decision.shayneNeumann
  australianLaborParty
  parliamentaryOfficeNoExecutiveInference
  electorateRepresentationRoute
  "Shayne Neumann is the Australian Labor Party Member for Blair; party/electorate representation does not confer EPBC approval power."
  "Parliament of Australia current member/committee profile"
  true

charisMullenAlignment : PoliticalAlignmentReceipt
charisMullenAlignment = political-alignment-receipt
  Decision.charisMullen
  australianLaborParty
  queenslandOpposition
  electorateRepresentationRoute
  "Charis Mullen is the ALP Member for Jordan and currently serves in the Queensland Opposition."
  "Queensland Parliament member profile"
  true

andrewPowellAlignment : PoliticalAlignmentReceipt
andrewPowellAlignment = political-alignment-receipt
  Decision.andrewPowell
  liberalNationalPartyQueensland
  queenslandGovernment
  stateProtectionMinisterRoute
  "Andrew Powell is an LNP member and Queensland Minister for the Environment and Tourism and Minister for Science and Innovation."
  "Queensland Parliament member profile"
  true

------------------------------------------------------------------------
-- Cross-level strategy surface.
------------------------------------------------------------------------

record CrossLevelAdvocacySurface : Set where
  constructor cross-level-advocacy-surface
  field
    federalLaborPortfolioRoutePresent : Bool
    federalLaborRepresentativeRoutePresent : Bool
    stateLaborOppositionRepresentativeRoutePresent : Bool
    stateLNPEnvironmentMinisterRoutePresent : Bool
    exactFederalDelegateRoutePresent : Bool
    samePartyCoordinationProven : Bool
    bipartisanProtectionOutcomeProven : Bool

canonicalCrossLevelAdvocacySurface : CrossLevelAdvocacySurface
canonicalCrossLevelAdvocacySurface =
  cross-level-advocacy-surface true true true true true false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SamePartyCreatesCoordination : Set where
data SamePartyCreatesLegalAuthority : Set where
data PartyAlignmentPaysStatutoryTest : Set where
data OppositionMemberCanExerciseMinisterialPower : Set where
data MinisterialSupportBindsDelegate : Set where

samePartyDoesNotProveCoordination : SamePartyCreatesCoordination → ⊥
samePartyDoesNotProveCoordination ()

samePartyDoesNotCreateLegalAuthority : SamePartyCreatesLegalAuthority → ⊥
samePartyDoesNotCreateLegalAuthority ()

partyAlignmentDoesNotPayStatutoryTest : PartyAlignmentPaysStatutoryTest → ⊥
partyAlignmentDoesNotPayStatutoryTest ()

oppositionMemberDoesNotAcquireMinisterialPower : OppositionMemberCanExerciseMinisterialPower → ⊥
oppositionMemberDoesNotAcquireMinisterialPower ()

ministerialSupportDoesNotBindDelegateByDefinition : MinisterialSupportBindsDelegate → ⊥
ministerialSupportDoesNotBindDelegateByDefinition ()
