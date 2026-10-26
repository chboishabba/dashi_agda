module DASHI.Governance.OriginalThreadParetoMaxCut20261008Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.OriginalThreadParetoAcquisitionExact as Previous
import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.IRISDenaCorrectionAwareReviewGateExact as HansardReview
import DASHI.Governance.IRISDenaSameObjectAcquisitionMaxCutExact as IRIS
import DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact as Sovereignty
import DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact as Authority
import DASHI.Governance.AUKUSPersonnelExchangeMOUExistenceExact as MOU
import DASHI.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelopeExact as USPEP
import DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact as Briefing
import DASHI.Governance.IRISDenaBunkClaimRevisionConflictExact as Bunks
import DASHI.Governance.IRISDenaPublicRecordConsumerNonDescentExact as NonDescent
import DASHI.Governance.IranThreatRepressionCaseNarrowingExact as Iran

------------------------------------------------------------------------
-- 2026-10-14 ORIGINAL-THREAD PARETO RECOMPUTATION
--
-- Newly paid beneath the live frontier:
--   * generic U.S. PEP statutory/program envelope, including Australia as a
--     partner and the fully-integrated host-service program model;
--   * the earlier secondary "ordered to bunks" proposition is superseded for
--     claim evaluation by a later named primary Chief-of-Navy denial;
--   * the Hansard leaf now has an exact review contract reusing the generic
--     REAL-MATTER human-review + exact-item-binding machinery on master.
--
-- The review contract does not pay the empirical leaf: transcript/correction
-- content still has to be acquired, correction applicability resolved, and an
-- exact review receipt bound to the same duty-class proposition.
--
-- None of these results substitutes for correction-aware hearing content,
-- bilateral operative authority text, or the same-episode exact-duty record.
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
  "Acquire FADT transcript ref. 29619 pp. 49-52 and any applicable Chief of Navy correction, resolve correction applicability, and bind an exact human-review receipt to the same duty-class proposition before promotion. Acquisition or review alone does not create primary authority or historical truth."

embeddingProtocolCell : Pareto.RequirementCandidate LiveRequirement
embeddingProtocolCell = Pareto.requirement-candidate
  irisEmbeddingProtocolOperativeText
  true true true true
  2 6
  "Acquire the complete December 2024 Chief of Navy directive and operative bilateral MOU text/annexes. Generic U.S. PEP statutory/program authority, Australia-partner status, MOU existence/purpose, and secondary-reproduced direction/no-command clauses are already paid at their proper source roles; only the bilateral operative authority/third-party-hostilities fibre remains unpaid."

exactOperationalCell : Pareto.RequirementCandidate LiveRequirement
exactOperationalCell = Pareto.requirement-candidate
  irisExactOperationalRecord
  true true true true
  5 8
  "Acquire watchbill/duty assignment, action log, debrief or equivalent same-episode record identifying what the three Australians actually did during the IRIS Dena engagement. Public, duty-class and protocol observers are formally insufficient for this exact-task consumer."

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
  "More countries/actors/theories remain deferred until the live same-object IRIS acquisition cells are paid or shown acquisition-blocked."

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
-- Paid source/authority payloads remain distinct from routing scores.
------------------------------------------------------------------------

correctionAwarePrimaryBundle : Hansard.CorrectionAwarePrimaryBundle
correctionAwarePrimaryBundle = Hansard.canonicalPrimaryBundle

correctionAwareReviewDemand : HansardReview.CorrectionAwareReviewDemand
correctionAwareReviewDemand = HansardReview.canonicalReviewDemand

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

usPEPAuthorityEnvelope : USPEP.USPEPAuthorityEnvelopeReceipt
usPEPAuthorityEnvelope = USPEP.canonicalEnvelope

bunkClaimRevision : Bunks.BunkClaimRevisionReceipt
bunkClaimRevision = Bunks.canonicalRevision

publicRecordNonDescent :
  Descent.ConsumerNonDescentWitness
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
