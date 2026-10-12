module DASHI.Governance.OriginalThreadParetoMaxCut20261008Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.OriginalThreadParetoAcquisitionExact as Previous
import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.IRISDenaSameObjectAcquisitionMaxCutExact as IRIS
import DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact as Sovereignty
import DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact as Authority
import DASHI.Governance.AUKUSPersonnelExchangeMOUExistenceExact as MOU
import DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact as Briefing
import DASHI.Governance.IRISDenaPublicRecordConsumerNonDescentExact as NonDescent
import DASHI.Governance.IranThreatRepressionCaseNarrowingExact as Iran

------------------------------------------------------------------------
-- 2026-10-12 ORIGINAL-THREAD PARETO RECOMPUTATION
--
-- Prior paid cells remain paid in Previous. This owner recomputes only the
-- residual programme after establishing that:
--   * transcript ref. 29619 is published in full;
--   * later Chief of Navy correction documents exist;
--   * the correct primary hearing object is correction-aware;
--   * official AUKUS/ASA sources pay existence and workforce purpose of the
--     Australia-US personnel-exchange MOU;
--   * leaked secondary reproductions narrow the 2024 embedded-authority
--     directive while leaving the directive/MOU operative text unacquired;
--   * exact duty does not descend through the current public-record observer;
--   * statutory coverage, direction authority, formal command, national-policy
--     constraint and actual duty are separate sovereignty coordinates.
------------------------------------------------------------------------

data LiveRequirement : Set where
  irisCorrectionAwareHansardContent : LiveRequirement
  irisEmbeddingProtocolOperativeText : LiveRequirement
  irisExactOperationalRecord : LiveRequirement
  iranMarginalRepressionIncrement : LiveRequirement
  broadHistoricalExpansion : LiveRequirement

hansardContentCell : Pareto.RequirementCandidate LiveRequirement
hansardContentCell = Pareto.requirement-candidate
  irisCorrectionAwareHansardContent
  true true true true
  1 5
  "Read FADT transcript ref. 29619 pp. 49-52 together with any applicable Chief of Navy correction; promote/correct defensive/platform-maintenance duty classes only from that primary bundle."

embeddingProtocolCell : Pareto.RequirementCandidate LiveRequirement
embeddingProtocolCell = Pareto.requirement-candidate
  irisEmbeddingProtocolOperativeText
  true true true true
  2 6
  "Acquire the complete December 2024 Chief of Navy directive and the operative text/annexes of the Australia-US personnel-exchange MOU. Primary official sources already pay MOU existence and workforce purpose; secondary reporting attributes lawful/reasonable USN direction authority plus an explicit no-command clause. Only the operative authority/third-party-hostilities content remains unpaid."

exactOperationalCell : Pareto.RequirementCandidate LiveRequirement
exactOperationalCell = Pareto.requirement-candidate
  irisExactOperationalRecord
  true true true true
  5 8
  "Acquire watchbill/duty assignment, action log, debrief or equivalent same-episode record identifying what the three Australians actually did during the IRIS Dena engagement. Canonical consumer non-descent now proves the existing public surface cannot by itself determine this outcome."

iranMarginalCell : Pareto.RequirementCandidate LiveRequirement
iranMarginalCell = Pareto.requirement-candidate
  iranMarginalRepressionIncrement
  true true true true
  5 5
  "Still required: identify the marginal 2026 Iranian repression increment attributable to external threat; qualitative wartime routing is already paid."

broadExpansionCell : Pareto.RequirementCandidate LiveRequirement
broadExpansionCell = Pareto.requirement-candidate
  broadHistoricalExpansion
  false true true false
  5 2
  "More countries/actors/theories are deferred until the live same-object IRIS acquisition cells are paid or shown acquisition-blocked."

livePortfolio : List (Pareto.RequirementCandidate LiveRequirement)
livePortfolio =
  hansardContentCell
  ∷ embeddingProtocolCell
  ∷ exactOperationalCell
  ∷ iranMarginalCell
  ∷ broadExpansionCell
  ∷ []

hansardContentOnFrontier :
  Pareto.onParetoFrontier? livePortfolio hansardContentCell ≡ true
hansardContentOnFrontier = refl

embeddingProtocolOnFrontier :
  Pareto.onParetoFrontier? livePortfolio embeddingProtocolCell ≡ true
embeddingProtocolOnFrontier = refl

exactOperationalOnFrontier :
  Pareto.onParetoFrontier? livePortfolio exactOperationalCell ≡ true
exactOperationalOnFrontier = refl

iranMarginalCurrentlyDominated :
  Pareto.onParetoFrontier? livePortfolio iranMarginalCell ≡ false
iranMarginalCurrentlyDominated = refl

broadExpansionDeferred :
  Pareto.eligible? broadExpansionCell ≡ false
broadExpansionDeferred = refl

frontierExactlyIRISThreeStage :
  Pareto.paretoFrontier livePortfolio ≡
    hansardContentCell ∷ embeddingProtocolCell ∷ exactOperationalCell ∷ []
frontierExactlyIRISThreeStage = refl

------------------------------------------------------------------------
-- Source/authority payloads remain separate from routing scores.
------------------------------------------------------------------------

correctionAwarePrimaryBundle : Hansard.CorrectionAwarePrimaryBundle
correctionAwarePrimaryBundle = Hansard.canonicalPrimaryBundle

irisMinCut : IRIS.RemainingMinCut
irisMinCut = IRIS.currentMinCut

sovereigntyBoundary : Sovereignty.AUKUSCommandSovereigntyBoundary
sovereigntyBoundary = Sovereignty.canonicalBoundary

embeddedAuthorityBoundary : Authority.DirectionCommandBoundary
embeddedAuthorityBoundary = Authority.canonicalBoundary

embeddedDirectiveResidual : Authority.PrimaryDocumentResidual
embeddedDirectiveResidual = Authority.directiveResidual

mouExistenceReceipt : MOU.MOUExistenceReceipt
mouExistenceReceipt = MOU.canonicalMOUExistence

mouOperativeResidual : MOU.RemainingMOUResidual
mouOperativeResidual = MOU.operativeMOUResidual

publicRecordNonDescent :
  NonDescent.Descent.ConsumerNonDescentWitness
    NonDescent.publicObserver
    NonDescent.exactDutyConsumer
publicRecordNonDescent = NonDescent.publicRecordNonDescent

ministerialBriefingFOIBoundary : Briefing.MinisterialBriefingFOIReceipt
ministerialBriefingFOIBoundary = Briefing.canonicalReceipt

iranResidual : Iran.SameEpisodeResidual
iranResidual = Iran.sameEpisodeResidual

previousPortfolio :
  List (Pareto.RequirementCandidate Previous.OriginalThreadRequirement)
previousPortfolio = Previous.originalThreadPortfolio
