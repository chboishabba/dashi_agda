module DASHI.Policy.AustraliaPalestineResponseIntensityGapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as ABC
import DASHI.Policy.ABC730RationaleSalienceDecisionFunctionExact as Salience
import DASHI.Policy.AustraliaIsraelGaslightingPoliticalEconomyBridgeExact as PoliticalEconomy
import DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact as AUIS

------------------------------------------------------------------------
-- Australia / Palestine response-intensity owner.
--
-- The web-verified state is not literal non-response: Australia has recognised
-- Palestine, funded humanitarian/recovery assistance, and imposed targeted
-- sanctions on violent settlers/entities.  The live question is whether those
-- actions are commensurate with the harms and causal mechanisms the government
-- itself says are destroying the viability of a Palestinian state.
------------------------------------------------------------------------

data ResponseKind : Set where
  diplomaticRecognition : ResponseKind
  humanitarianAssistance : ResponseKind
  institutionBuilding : ResponseKind
  targetedSettlerSanctions : ResponseKind
  broaderSettlementEconomicConstraint : ResponseKind
  defenceIndustrialDecoupling : ResponseKind

data ResponseStatus : Set where
  implemented : ResponseStatus
  declined : ResponseStatus
  unresolved : ResponseStatus

record ResponseReceipt : Set where
  constructor responseReceipt
  field
    kind : ResponseKind
    status : ResponseStatus
    sourceReference : String
    boundedDescription : String

open ResponseReceipt public

recognitionReceipt : ResponseReceipt
recognitionReceipt = responseReceipt diplomaticRecognition implemented
  "Australian PM/Foreign Minister, 21 Sep 2025"
  "Australia formally recognised the independent and sovereign State of Palestine."

humanitarianReceipt : ResponseReceipt
humanitarianReceipt = responseReceipt humanitarianAssistance implemented
  "DFAT / Foreign Minister humanitarian releases 2025-26"
  "Australia provided substantial humanitarian assistance for civilians in Gaza and Lebanon, including additional 2025 packages and continuing Palestine ODA/UNRWA funding."

institutionBuildingReceipt : ResponseReceipt
institutionBuildingReceipt = responseReceipt institutionBuilding implemented
  "Foreign Minister / International Development Minister, 21 Jul 2026"
  "Australia announced support for Gaza recovery and Palestinian Authority institutional, governance and economic reform."

targetedSettlerSanctionsReceipt : ResponseReceipt
targetedSettlerSanctionsReceipt = responseReceipt targetedSettlerSanctions implemented
  "Foreign Minister, 2 and 9 Jun 2026"
  "Australia imposed targeted sanctions on additional Israeli individuals/entities associated with settler violence and joined coordinated measures with partners."

broaderSettlementConstraintReceipt : ResponseReceipt
broaderSettlementConstraintReceipt = responseReceipt broaderSettlementEconomicConstraint declined
  "ABC 7.30 / Senate reporting, 9 Sep 2026"
  "Australia declined at that time to join the broader UK-style settlement import/economic ban, citing implementation concerns, unintended consequences and other rationales."

defenceDecouplingReceipt : ResponseReceipt
defenceDecouplingReceipt = responseReceipt defenceIndustrialDecoupling unresolved
  "DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact"
  "Existing military-industrial links remain separately recorded; no blanket defence-industrial decoupling is established by this lane."

------------------------------------------------------------------------
-- Intensity-gap analysis.
------------------------------------------------------------------------

data ResponseIntensityClaim : Set where
  literalNoResponse : ResponseIntensityClaim
  nonZeroPalestineSupportExists : ResponseIntensityClaim
  governmentAcknowledgesSettlementThreat : ResponseIntensityClaim
  broaderEconomicResponseDeclined : ResponseIntensityClaim
  responseMayBeIncommensurateWithStatedThreat : ResponseIntensityClaim
  incommensurabilityProvesBadFaith : ResponseIntensityClaim

data Disposition : Set where
  supported : Disposition
  contradicted : Disposition
  boundedInference : Disposition
  unresolvedCausation : Disposition

record IntensityReceipt : Set where
  constructor intensityReceipt
  field
    claim : ResponseIntensityClaim
    disposition : Disposition
    sourceReference : String
    statement : String

open IntensityReceipt public

literalNoResponseRefuted : IntensityReceipt
literalNoResponseRefuted = intensityReceipt literalNoResponse contradicted
  "recognition + aid + targeted sanctions + institution-building receipts"
  "A literal claim that Labor/Australia made no response for Palestine is false on the current source surface."

nonZeroSupportReceipt : IntensityReceipt
nonZeroSupportReceipt = intensityReceipt nonZeroPalestineSupportExists supported
  "Australian Government primary sources 2025-26"
  "Australia has taken concrete diplomatic, humanitarian, institution-building and targeted-sanctions actions that are supportive of Palestinian civilians/statehood."

governmentThreatReceipt : IntensityReceipt
governmentThreatReceipt = intensityReceipt governmentAcknowledgesSettlementThreat supported
  "ABC730 C040-C042; Foreign Minister 2/9 Jun 2026"
  "The government itself says settlement expansion, E1 and settler violence undermine or extinguish the viability of a Palestinian state."

broaderResponseDeclinedReceipt : IntensityReceipt
broaderResponseDeclinedReceipt = intensityReceipt broaderEconomicResponseDeclined supported
  "ABC730 C026-C036"
  "Australia nevertheless declined the broader UK-style settlement-economic ban while partners moved further."

responseIntensityGap : IntensityReceipt
responseIntensityGap = intensityReceipt responseMayBeIncommensurateWithStatedThreat boundedInference
  "comparison of implemented responses with the government's own stated threat model"
  "There is a legitimate response-intensity question: whether recognition, aid and targeted sanctions are commensurate with the scale and causal mechanisms of settlement expansion that Australia itself says threaten Palestinian statehood."

badFaithStillOpen : IntensityReceipt
badFaithStillOpen = intensityReceipt incommensurabilityProvesBadFaith unresolvedCausation
  "requires decision-chain, weighting and intent evidence"
  "A response-intensity gap does not by itself prove deception, policy capture or bad faith."

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ResponseBoundary : Set where
  constructor responseBoundary
  field
    symbolicOrTargetedActionEqualsAdequateResponse : Bool
    symbolicOrTargetedActionEqualsAdequateResponseIsFalse : symbolicOrTargetedActionEqualsAdequateResponse ≡ false
    nonZeroSupportErasesMaterialContradictions : Bool
    nonZeroSupportErasesMaterialContradictionsIsFalse : nonZeroSupportErasesMaterialContradictions ≡ false
    inadequateResponseAutomaticallyProvesHostileIntent : Bool
    inadequateResponseAutomaticallyProvesHostileIntentIsFalse : inadequateResponseAutomaticallyProvesHostileIntent ≡ false
    responseIntensityIsValidConsumer : Bool
    responseIntensityIsValidConsumerIsTrue : responseIntensityIsValidConsumer ≡ true

canonicalResponseBoundary : ResponseBoundary
canonicalResponseBoundary = responseBoundary false refl false refl false refl true refl
