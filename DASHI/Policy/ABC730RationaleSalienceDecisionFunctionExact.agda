module DASHI.Policy.ABC730RationaleSalienceDecisionFunctionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as ABC
import DASHI.Policy.AustraliaIsraelGaslightingPoliticalEconomyBridgeExact as PoliticalEconomy
import DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact as AUIS
import DASHI.Law.AustralianMajorPartyDonationDisclosureExact as Finance
import DASHI.Law.AustraliaIsraelInfluenceLobbyingSpeechGovernanceExact as Influence

------------------------------------------------------------------------
-- ABC 7.30 rationale-salience / decision-function boundary.
--
-- The recovered 9-Sep-2026 transcript does not present one unitary reason for
-- Australia's refusal to join the UK-style settlement ban.  It foregrounds
-- implementation / "unintended consequences" and separately records other
-- rationales and political context.  This owner formalises that asymmetry
-- without inferring an undisclosed motive or policy capture by fiat.
------------------------------------------------------------------------

data RationaleCoordinate : Set where
  implementationDifficulty : RationaleCoordinate
  unintendedAustralianBusinessConsequences : RationaleCoordinate
  unintendedPalestinianConsequences : RationaleCoordinate
  unintendedIsraeliConsequences : RationaleCoordinate
  tradingNationConcern : RationaleCoordinate
  bluntInstrumentConcern : RationaleCoordinate
  twoStateEffectivenessUncertainty : RationaleCoordinate
  antiBDSPoliticalHistory : RationaleCoordinate
  existingTargetedMeasures : RationaleCoordinate
  israelWelcomesAustralianNonParticipation : RationaleCoordinate
  defenceIndustrialConstraintHypothesis : RationaleCoordinate
  donorAccessConstraintHypothesis : RationaleCoordinate
  lobbyingConstraintHypothesis : RationaleCoordinate


data RationaleStatus : Set where
  transcriptForegrounded : RationaleStatus
  transcriptAcknowledged : RationaleStatus
  contextualOnly : RationaleStatus
  externalStructuralCoordinate : RationaleStatus
  unresolvedDecisionCause : RationaleStatus

record RationaleReceipt : Set where
  constructor rationaleReceipt
  field
    coordinate : RationaleCoordinate
    status : RationaleStatus
    sourceReference : String
    statement : String

open RationaleReceipt public

implementationReceipt : RationaleReceipt
implementationReceipt = rationaleReceipt implementationDifficulty transcriptForegrounded
  "ABC730 C029 / transcript line 22"
  "Australia publicly foregrounded implementation concerns when declining the blanket-style import ban."

businessConsequenceReceipt : RationaleReceipt
businessConsequenceReceipt = rationaleReceipt unintendedAustralianBusinessConsequences transcriptForegrounded
  "ABC730 C029 / transcript line 22"
  "Australian businesses were named as a class potentially exposed to unintended consequences; mechanism and sign were not specified in the recovered transcript."

palestinianConsequenceReceipt : RationaleReceipt
palestinianConsequenceReceipt = rationaleReceipt unintendedPalestinianConsequences transcriptForegrounded
  "ABC730 C029 / transcript line 22"
  "Palestinians were named as a class potentially exposed to unintended consequences; mechanism and sign were not specified in the recovered transcript."

israeliConsequenceReceipt : RationaleReceipt
israeliConsequenceReceipt = rationaleReceipt unintendedIsraeliConsequences transcriptForegrounded
  "ABC730 C029 / transcript line 22"
  "Israelis were named as a class potentially exposed to unintended consequences; mechanism and sign were not specified in the recovered transcript."

tradingNationReceipt : RationaleReceipt
tradingNationReceipt = rationaleReceipt tradingNationConcern transcriptAcknowledged
  "ABC730 C036 / transcript line 28"
  "ABC explicitly reports Australia's status as a trading nation as another reason advanced against joining the UK-style ban."

bluntInstrumentReceipt : RationaleReceipt
bluntInstrumentReceipt = rationaleReceipt bluntInstrumentConcern transcriptAcknowledged
  "ABC730 C036 / transcript line 28"
  "ABC explicitly reports the view that the UK-style ban is a blunt instrument as another reason advanced against it."

twoStateEffectivenessReceipt : RationaleReceipt
twoStateEffectivenessReceipt = rationaleReceipt twoStateEffectivenessUncertainty transcriptAcknowledged
  "ABC730 C033 / transcript line 24"
  "A government-defending voice argues that the objective is a two-state solution and expresses uncertainty that the sanctions advance that objective."

antiBDSHistoryReceipt : RationaleReceipt
antiBDSHistoryReceipt = rationaleReceipt antiBDSPoliticalHistory contextualOnly
  "ABC730 C037 / transcript line 28"
  "ABC reminds viewers that Anthony Albanese has a long political history of conflict with the Greens over boycott, divestment and sanctions against Israel. The transcript supplies context, not proof that this history caused the present decision."

targetedMeasuresReceipt : RationaleReceipt
targetedMeasuresReceipt = rationaleReceipt existingTargetedMeasures transcriptAcknowledged
  "ABC730 C035/C040 / transcript lines 26-32"
  "Australia presents targeted measures against sanctioned settlers/settlement activity as its preferred alternative to the broader UK-style ban."

israeliWelcomeReceipt : RationaleReceipt
israeliWelcomeReceipt = rationaleReceipt israelWelcomesAustralianNonParticipation contextualOnly
  "ABC730 C027 / transcript line 22"
  "ABC reports that Israel's ambassador welcomed Australia's decision not to join the blanket ban; diplomatic preference does not establish decision causation."

------------------------------------------------------------------------
-- Counter-rationale material inside the same ABC interview.
------------------------------------------------------------------------

data CounterRationaleCoordinate : Set where
  rulesOfOriginDifferentiationAlreadyExists : CounterRationaleCoordinate
  settlementTradeVolumeReportedSmall : CounterRationaleCoordinate
  measureTargetsFinanceAndProfessionalServices : CounterRationaleCoordinate
  settlementFlatsAdvertisedInLondon : CounterRationaleCoordinate
  ukFramesActionAsLegalMoralNonParticipation : CounterRationaleCoordinate

record CounterRationaleReceipt : Set where
  constructor counterRationaleReceipt
  field
    counterCoordinate : CounterRationaleCoordinate
    sourceReference : String
    boundedStatement : String

open CounterRationaleReceipt public

rulesOfOriginReceipt : CounterRationaleReceipt
rulesOfOriginReceipt = counterRationaleReceipt rulesOfOriginDifferentiationAlreadyExists
  "ABC730 Thornberry interview / transcript lines 62-68"
  "Thornberry argues that the UK already distinguishes Israel proper from Palestinian/West Bank origin in trade administration and can therefore manage rules-of-origin differentiation."

smallTradeReceipt : CounterRationaleReceipt
smallTradeReceipt = counterRationaleReceipt settlementTradeVolumeReportedSmall
  "ABC730 Thornberry interview / transcript lines 68-70"
  "Thornberry says the amount of UK trade with settlements is understood to be very small; exact magnitude remains externally verifiable."

servicesReceipt : CounterRationaleReceipt
servicesReceipt = counterRationaleReceipt measureTargetsFinanceAndProfessionalServices
  "ABC730 C047 / transcript lines 42-44"
  "The described UK measure targets not only goods but financial and professional support for settlement construction, including mortgages and architects."

flatsReceipt : CounterRationaleReceipt
flatsReceipt = counterRationaleReceipt settlementFlatsAdvertisedInLondon
  "ABC730 C046 / transcript lines 42-44"
  "Thornberry says settlement-project flats had been advertised in London, supplying a concrete service/real-estate pathway rather than an abstract boycott target."

legalMoralReceipt : CounterRationaleReceipt
legalMoralReceipt = counterRationaleReceipt ukFramesActionAsLegalMoralNonParticipation
  "ABC730 Thornberry interview / transcript lines 70-72"
  "Thornberry frames the UK action as refusing participation in settlement-supporting economic activity on legal and moral grounds."

------------------------------------------------------------------------
-- Salience gap: what is foregrounded is not automatically the complete policy
-- objective function.  Conversely, the existence of other constraints does not
-- establish that any one of them secretly determined the decision.
------------------------------------------------------------------------

data DecisionFunctionClaim : Set where
  publicRationaleIsPlural : DecisionFunctionClaim
  palestinianConsequenceLanguageIsUnderSpecified : DecisionFunctionClaim
  transcriptContainsCounterEvidenceToImplementationObjection : DecisionFunctionClaim
  publicForegroundEqualsCompleteDecisionFunction : DecisionFunctionClaim
  defenceRelationsDetermineDecision : DecisionFunctionClaim
  donorRelationsDetermineDecision : DecisionFunctionClaim
  lobbyingRelationsDetermineDecision : DecisionFunctionClaim
  omittedConstraintInvestigationIsWarranted : DecisionFunctionClaim


data DecisionFunctionDisposition : Set where
  supported : DecisionFunctionDisposition
  boundedInference : DecisionFunctionDisposition
  unresolved : DecisionFunctionDisposition
  rejectedPromotion : DecisionFunctionDisposition

record DecisionFunctionReceipt : Set where
  constructor decisionFunctionReceipt
  field
    claim : DecisionFunctionClaim
    disposition : DecisionFunctionDisposition
    evidence : String
    interpretation : String

open DecisionFunctionReceipt public

pluralRationale : DecisionFunctionReceipt
pluralRationale = decisionFunctionReceipt publicRationaleIsPlural supported
  "ABC730 C029, C033, C036-C040"
  "The broadcast itself records multiple rationales/contextual constraints rather than a single Palestinian-protection justification."

palestinianUnderSpecification : DecisionFunctionReceipt
palestinianUnderSpecification = decisionFunctionReceipt palestinianConsequenceLanguageIsUnderSpecified boundedInference
  "ABC730 C029"
  "The Palestinian consequence coordinate is named without sign, mechanism, probability or concrete beneficiary/harm bearer."

implementationCounterEvidence : DecisionFunctionReceipt
implementationCounterEvidence = decisionFunctionReceipt transcriptContainsCounterEvidenceToImplementationObjection supported
  "ABC730 C045-C047 plus Thornberry rules-of-origin discussion lines 62-70"
  "The same program supplies an argument that differentiation is administratively feasible and that the measure can target specific settlement-support pathways."

foregroundIsCompleteRejected : DecisionFunctionReceipt
foregroundIsCompleteRejected = decisionFunctionReceipt publicForegroundEqualsCompleteDecisionFunction rejectedPromotion
  "ABC730 explicitly reports 'other reasons' at C036 and political context at C037"
  "The recovered broadcast does not warrant treating the foregrounded unintended-consequences formulation as an exhaustive description of the government's decision function."

defenceDecisionOpen : DecisionFunctionReceipt
defenceDecisionOpen = decisionFunctionReceipt defenceRelationsDetermineDecision unresolved
  "DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact"
  "Defence-industrial relations are a live structural coordinate but require decision-chain evidence before they can be promoted as a cause of the no-ban decision."

donorDecisionOpen : DecisionFunctionReceipt
donorDecisionOpen = decisionFunctionReceipt donorRelationsDetermineDecision unresolved
  "DASHI.Law.AustralianMajorPartyDonationDisclosureExact"
  "Published donation relations create an admissible influence hypothesis but do not establish this policy decision's cause."

lobbyingDecisionOpen : DecisionFunctionReceipt
lobbyingDecisionOpen = decisionFunctionReceipt lobbyingRelationsDetermineDecision unresolved
  "DASHI.Law.AustraliaIsraelInfluenceLobbyingSpeechGovernanceExact"
  "Documented overt lobbying/access creates an admissible constraint hypothesis but does not establish this decision's cause."

investigationWarranted : DecisionFunctionReceipt
investigationWarranted = decisionFunctionReceipt omittedConstraintInvestigationIsWarranted boundedInference
  "plural source-backed rationale surface + external defence/finance/lobbying coordinates"
  "Because the public rationale is non-exhaustive and several material institutional relationships exist, it is legitimate to seek Cabinet, DFAT, Defence, trade, lobbying and ministerial records that identify the actual weighted decision inputs."

record RationaleSalienceBoundary : Set where
  constructor rationaleSalienceBoundary
  field
    foregroundedReasonIsCompleteDecisionFunction : Bool
    foregroundedReasonIsCompleteDecisionFunctionIsFalse : foregroundedReasonIsCompleteDecisionFunction ≡ false
    acknowledgedOtherReasonProvesHiddenMotive : Bool
    acknowledgedOtherReasonProvesHiddenMotiveIsFalse : acknowledgedOtherReasonProvesHiddenMotive ≡ false
    counterRationaleProvesBadFaith : Bool
    counterRationaleProvesBadFaithIsFalse : counterRationaleProvesBadFaith ≡ false
    salienceGapJustifiesDecisionChainSearch : Bool
    salienceGapJustifiesDecisionChainSearchIsTrue : salienceGapJustifiesDecisionChainSearch ≡ true

canonicalRationaleSalienceBoundary : RationaleSalienceBoundary
canonicalRationaleSalienceBoundary = rationaleSalienceBoundary false refl false refl false refl true refl
