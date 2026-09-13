module DASHI.Policy.AustraliaIsraelGaslightingPoliticalEconomyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as ABC
import DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact as AUIS
import DASHI.Law.AustralianMajorPartyDonationDisclosureExact as Finance
import DASHI.Law.IsraeliAmalekContemporaryRoleBindingSourceReceiptsExact as Amalek

------------------------------------------------------------------------
-- Cross-pollination owner for the 9-Sep-2026 ABC 'gaslighting' discussion.
--
-- It does not redefine the source claims.  It composes already-owned transcript,
-- military/security, finance and Amalek provenance into explicit hypotheses and
-- firewalls.  The target is explanation and proof-search, not accusation by fiat.
------------------------------------------------------------------------

data ConsequenceTarget : Set where
  australianBusiness : ConsequenceTarget
  palestinianActors : ConsequenceTarget
  israeliActors : ConsequenceTarget
  bilateralStrategicRelations : ConsequenceTarget
  defenceIndustrialRelations : ConsequenceTarget

data ConsequenceSign : Set where
  beneficial : ConsequenceSign
  harmful : ConsequenceSign
  mixed : ConsequenceSign
  unspecified : ConsequenceSign

record UnintendedConsequenceCoordinate : Set where
  constructor unintendedConsequenceCoordinate
  field
    target : ConsequenceTarget
    sign : ConsequenceSign
    mechanismSpecified : Bool
    evidenceReference : String

open UnintendedConsequenceCoordinate public

wongBusinessConsequence : UnintendedConsequenceCoordinate
wongBusinessConsequence = unintendedConsequenceCoordinate australianBusiness unspecified false
  "ABC730 C029: implementation concerns and unintended consequences for Australian businesses, Palestinians and Israelis"

wongPalestinianConsequence : UnintendedConsequenceCoordinate
wongPalestinianConsequence = unintendedConsequenceCoordinate palestinianActors unspecified false
  "ABC730 C029: no sign or mechanism stated in the recovered transcript"

wongIsraeliConsequence : UnintendedConsequenceCoordinate
wongIsraeliConsequence = unintendedConsequenceCoordinate israeliActors unspecified false
  "ABC730 C029: no sign or mechanism stated in the recovered transcript"

------------------------------------------------------------------------
-- Policy-justification inversion hypothesis.
------------------------------------------------------------------------

data GaslightingAnalysisClaim : Set where
  phraseIsSemanticallyUnderspecified : GaslightingAnalysisClaim
  criticAllegesPolicyJustificationInversion : GaslightingAnalysisClaim
  laborAcknowledgesSettlementsThreatenPalestinianStatehood : GaslightingAnalysisClaim
  ukMeasureTargetsSettlementEconomicSupport : GaslightingAnalysisClaim
  australiaMaintainsIsraelLinkedDefenceRelations : GaslightingAnalysisClaim
  defenceRelationsCausedNoBanDecision : GaslightingAnalysisClaim
  donorRelationsCausedNoBanDecision : GaslightingAnalysisClaim
  israeliCovertInfluenceCausedNoBanDecision : GaslightingAnalysisClaim

data AnalysisDisposition : Set where
  sourceSupported : AnalysisDisposition
  boundedInference : AnalysisDisposition
  unresolvedCausation : AnalysisDisposition

record AnalysisReceipt : Set where
  constructor analysisReceipt
  field
    claim : GaslightingAnalysisClaim
    disposition : AnalysisDisposition
    sourceReference : String
    boundedStatement : String

open AnalysisReceipt public

underspecifiedConsequenceReceipt : AnalysisReceipt
underspecifiedConsequenceReceipt = analysisReceipt phraseIsSemanticallyUnderspecified boundedInference
  "ABC730 C029"
  "The phrase names affected classes but does not specify sign, mechanism, probability or concrete consequence in the recovered transcript."

inversionReceipt : AnalysisReceipt
inversionReceipt = analysisReceipt criticAllegesPolicyJustificationInversion sourceSupported
  "ABC730 C030-C032"
  "The critic juxtaposes support for Palestinian statehood with settlement expansion undermining that statehood, then characterises the stated rationale for inaction as 'unbelievable gaslighting from Labor'."

settlementThreatReceipt : AnalysisReceipt
settlementThreatReceipt = analysisReceipt laborAcknowledgesSettlementsThreatenPalestinianStatehood sourceSupported
  "ABC730 C040-C042"
  "The Australian government itself states that rapid settlement expansion, E1 and settler violence are extinguishing the possibility of a two-state solution while retaining a two-state solution as its stated objective."

ukEconomicSupportReceipt : AnalysisReceipt
ukEconomicSupportReceipt = analysisReceipt ukMeasureTargetsSettlementEconomicSupport sourceSupported
  "ABC730 C045-C047"
  "The Thornberry interview describes the UK measure as reaching settlement trade plus finance, mortgages, professional services, architects and London advertising of settlement flats."

defenceRelationReceipt : AnalysisReceipt
defenceRelationReceipt = analysisReceipt australiaMaintainsIsraelLinkedDefenceRelations sourceSupported
  "DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact"
  "Existing repo receipts record F-35 global-supply-chain participation, military export permits relating to Israel and Israeli defence-industry contracts while separately recording Palestine recognition and settler sanctions."

defenceCausationOpen : AnalysisReceipt
defenceCausationOpen = analysisReceipt defenceRelationsCausedNoBanDecision unresolvedCausation
  "requires Cabinet/DFAT/Defence/ministerial decision-chain evidence"
  "Material defence relations create a plausible incentive hypothesis but do not by themselves prove causation of the 2026 decision not to join the UK settlement ban."

donorCausationOpen : AnalysisReceipt
donorCausationOpen = analysisReceipt donorRelationsCausedNoBanDecision unresolvedCausation
  "DASHI.Law.AustralianMajorPartyDonationDisclosureExact"
  "Published political-finance relations may motivate an influence/access inquiry; donation records alone do not prove the sanctions position was donor-caused."

covertInfluenceCausationOpen : AnalysisReceipt
covertInfluenceCausationOpen = analysisReceipt israeliCovertInfluenceCausedNoBanDecision unresolvedCausation
  "separate influence-operation/source-diligence lane"
  "Documented capability or historical influence operations do not identify the Australian 2026 sanctions decision as an operation."

------------------------------------------------------------------------
-- Existing Amalek material is context, not a causal shortcut.
------------------------------------------------------------------------

record AmalekContextBoundary : Set where
  constructor amalekContextBoundary
  field
    contemporaryRoleBindingExists : Bool
    contemporaryRoleBindingExistsIsTrue : contemporaryRoleBindingExists ≡ true
    amalekRhetoricProvesAustralianPolicyCapture : Bool
    amalekRhetoricProvesAustralianPolicyCaptureIsFalse : amalekRhetoricProvesAustralianPolicyCapture ≡ false
    amalekRhetoricProvesSettlementBanDecisionCause : Bool
    amalekRhetoricProvesSettlementBanDecisionCauseIsFalse : amalekRhetoricProvesSettlementBanDecisionCause ≡ false

canonicalAmalekContextBoundary : AmalekContextBoundary
canonicalAmalekContextBoundary = amalekContextBoundary true refl false refl false refl

------------------------------------------------------------------------
-- Final non-collapse boundary.
------------------------------------------------------------------------

record PoliticalEconomyBoundary : Set where
  constructor politicalEconomyBoundary
  field
    vagueRationaleProvesDeception : Bool
    vagueRationaleProvesDeceptionIsFalse : vagueRationaleProvesDeception ≡ false
    policyInconsistencyProvesCovertOperation : Bool
    policyInconsistencyProvesCovertOperationIsFalse : policyInconsistencyProvesCovertOperation ≡ false
    defenceLinkPlusDonationProvesPolicyCapture : Bool
    defenceLinkPlusDonationProvesPolicyCaptureIsFalse : defenceLinkPlusDonationProvesPolicyCapture ≡ false
    theseCoordinatesJustifyCausalInvestigation : Bool
    theseCoordinatesJustifyCausalInvestigationIsTrue : theseCoordinatesJustifyCausalInvestigation ≡ true

canonicalPoliticalEconomyBoundary : PoliticalEconomyBoundary
canonicalPoliticalEconomyBoundary = politicalEconomyBoundary false refl false refl false refl true refl
