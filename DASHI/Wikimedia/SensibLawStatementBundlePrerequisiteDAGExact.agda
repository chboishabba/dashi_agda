module DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.QueryPromotionResidualBidiExact as Promotion
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.TemporalPromotionNonRetroactivityBidiExact as Temporal
import DASHI.Wikimedia.SensibLawStatementBundleDiagnosisProofSearchExact as Search

------------------------------------------------------------------------
-- STATEMENT-BUNDLE PREREQUISITE DAG / MINIMAL OPEN CUT
--
-- The terminal semantic-correspondence theorem is not the first thing to try.
-- It is downstream of a finite prerequisite surface.  The first unpaid node
-- selects the next producer/mechanism; producer selection is not payment.
------------------------------------------------------------------------

data BundleObligation : Set where
  sameCarrier
  sourceSupport
  qualifierTransport
  rankTreatment
  provenanceSupport
  semanticCorrespondence
  : BundleObligation

record BundleObligationStatus : Set where
  constructor bundle-obligation-status
  field
    sameCarrierPaid : Bool
    sourceSupportPaid : Bool
    qualifierTransportPaid : Bool
    rankTreatmentPaid : Bool
    provenanceSupportPaid : Bool
    semanticCorrespondencePaid : Bool
open BundleObligationStatus public

data BundlePrerequisiteResidual : Set where
  missingSameCarrier
  missingSourceSupport
  missingQualifierTransport
  missingRankTreatment
  missingProvenanceSupport
  missingSemanticCorrespondence
  bundlePrerequisitesClosed
  : BundlePrerequisiteResidual

firstMissingPrerequisite : BundleObligationStatus → BundlePrerequisiteResidual
firstMissingPrerequisite (bundle-obligation-status false s q r p c) = missingSameCarrier
firstMissingPrerequisite (bundle-obligation-status true false q r p c) = missingSourceSupport
firstMissingPrerequisite (bundle-obligation-status true true false r p c) = missingQualifierTransport
firstMissingPrerequisite (bundle-obligation-status true true true false p c) = missingRankTreatment
firstMissingPrerequisite (bundle-obligation-status true true true true false c) = missingProvenanceSupport
firstMissingPrerequisite (bundle-obligation-status true true true true true false) = missingSemanticCorrespondence
firstMissingPrerequisite (bundle-obligation-status true true true true true true) = bundlePrerequisitesClosed

obligationForResidual : BundlePrerequisiteResidual → BundleObligation
obligationForResidual missingSameCarrier = sameCarrier
obligationForResidual missingSourceSupport = sourceSupport
obligationForResidual missingQualifierTransport = qualifierTransport
obligationForResidual missingRankTreatment = rankTreatment
obligationForResidual missingProvenanceSupport = provenanceSupport
obligationForResidual missingSemanticCorrespondence = semanticCorrespondence
obligationForResidual bundlePrerequisitesClosed = semanticCorrespondence

data BundlePrerequisiteProducer : Set where
  verifySameCarrier
  acquireSourceSupport
  proveQualifierTransport
  reviewRankTreatment
  acquireProvenanceSupport
  proveSemanticCorrespondence
  noPrerequisiteProducer
  : BundlePrerequisiteProducer

producerForResidual : BundlePrerequisiteResidual → BundlePrerequisiteProducer
producerForResidual missingSameCarrier = verifySameCarrier
producerForResidual missingSourceSupport = acquireSourceSupport
producerForResidual missingQualifierTransport = proveQualifierTransport
producerForResidual missingRankTreatment = reviewRankTreatment
producerForResidual missingProvenanceSupport = acquireProvenanceSupport
producerForResidual missingSemanticCorrespondence = proveSemanticCorrespondence
producerForResidual bundlePrerequisitesClosed = noPrerequisiteProducer

data PrerequisiteMechanism : Set where
  thinkMechanism lookMechanism reviewMechanism noMechanism : PrerequisiteMechanism

mechanismForProducer : BundlePrerequisiteProducer → PrerequisiteMechanism
mechanismForProducer verifySameCarrier = lookMechanism
mechanismForProducer acquireSourceSupport = lookMechanism
mechanismForProducer proveQualifierTransport = thinkMechanism
mechanismForProducer reviewRankTreatment = reviewMechanism
mechanismForProducer acquireProvenanceSupport = lookMechanism
mechanismForProducer proveSemanticCorrespondence = thinkMechanism
mechanismForProducer noPrerequisiteProducer = noMechanism

------------------------------------------------------------------------
-- Exact DAG edges.  These are prerequisite edges, not causal or authority
-- edges.  Their orientation is prerequisite -> dependent obligation.
------------------------------------------------------------------------

record PrerequisiteEdge : Set where
  constructor prerequisite-edge
  field
    prerequisite : BundleObligation
    dependent : BundleObligation
    edgeReference : String
open PrerequisiteEdge public

sameCarrierToSemantic : PrerequisiteEdge
sameCarrierToSemantic = prerequisite-edge sameCarrier semanticCorrespondence
  "same statement-bundle carrier is prerequisite to terminal semantic correspondence"

sourceSupportToSemantic : PrerequisiteEdge
sourceSupportToSemantic = prerequisite-edge sourceSupport semanticCorrespondence
  "bounded source support is prerequisite to terminal semantic correspondence"

qualifierTransportToSemantic : PrerequisiteEdge
qualifierTransportToSemantic = prerequisite-edge qualifierTransport semanticCorrespondence
  "qualifier-preserving transport is prerequisite to terminal semantic correspondence"

rankTreatmentToSemantic : PrerequisiteEdge
rankTreatmentToSemantic = prerequisite-edge rankTreatment semanticCorrespondence
  "consumer-relative rank treatment is prerequisite to terminal semantic correspondence"

provenanceSupportToSemantic : PrerequisiteEdge
provenanceSupportToSemantic = prerequisite-edge provenanceSupport semanticCorrespondence
  "independent provenance support is prerequisite to terminal semantic correspondence"

semanticPrerequisiteEdges : List PrerequisiteEdge
semanticPrerequisiteEdges =
  sameCarrierToSemantic ∷
  sourceSupportToSemantic ∷
  qualifierTransportToSemantic ∷
  rankTreatmentToSemantic ∷
  provenanceSupportToSemantic ∷ []

------------------------------------------------------------------------
-- Minimal open cut: for this finite linearized prerequisite policy, the first
-- unpaid prerequisite is the least work cut.  Later stages do not leapfrog it.
------------------------------------------------------------------------

record MinimalOpenPrerequisiteCut (status : BundleObligationStatus) : Set where
  constructor minimal-open-prerequisite-cut
  field
    firstResidual : BundlePrerequisiteResidual
    firstResidualExact : firstResidual ≡ firstMissingPrerequisite status
    producer : BundlePrerequisiteProducer
    producerExact : producer ≡ producerForResidual firstResidual
    mechanism : PrerequisiteMechanism
    mechanismExact : mechanism ≡ mechanismForProducer producer
    cutReference : String
open MinimalOpenPrerequisiteCut public

minimalCutFor : (status : BundleObligationStatus) → MinimalOpenPrerequisiteCut status
minimalCutFor status =
  minimal-open-prerequisite-cut
    (firstMissingPrerequisite status)
    refl
    (producerForResidual (firstMissingPrerequisite status))
    refl
    (mechanismForProducer (producerForResidual (firstMissingPrerequisite status)))
    refl
    "first unpaid bundle prerequisite; terminal semantic theorem remains downstream"

------------------------------------------------------------------------
-- Nat/Climate calibration: same carrier is already identified, but source
-- support is still missing.  We therefore Look for source support before any
-- qualifier-transport or terminal-semantic proof search.
------------------------------------------------------------------------

natCurrentPrerequisites : BundleObligationStatus
natCurrentPrerequisites =
  bundle-obligation-status true false false false false false

natCurrentCut : MinimalOpenPrerequisiteCut natCurrentPrerequisites
natCurrentCut = minimalCutFor natCurrentPrerequisites

natFirstMissingIsSourceSupport :
  firstResidual natCurrentCut ≡ missingSourceSupport
natFirstMissingIsSourceSupport = refl

natCurrentProducerIsSourceAcquisition :
  producer natCurrentCut ≡ acquireSourceSupport
natCurrentProducerIsSourceAcquisition = refl

natCurrentMechanismIsLook :
  mechanism natCurrentCut ≡ lookMechanism
natCurrentMechanismIsLook = refl

natAfterSourceSupport : BundleObligationStatus
natAfterSourceSupport =
  bundle-obligation-status true true false false false false

natAfterSourceCut : MinimalOpenPrerequisiteCut natAfterSourceSupport
natAfterSourceCut = minimalCutFor natAfterSourceSupport

natAfterSourceFirstMissingQualifierTransport :
  firstResidual natAfterSourceCut ≡ missingQualifierTransport
natAfterSourceFirstMissingQualifierTransport = refl

natAfterSourceMechanismIsThink :
  mechanism natAfterSourceCut ≡ thinkMechanism
natAfterSourceMechanismIsThink = refl

natBeforeTerminalSemantic : BundleObligationStatus
natBeforeTerminalSemantic =
  bundle-obligation-status true true true true true false

natTerminalCut : MinimalOpenPrerequisiteCut natBeforeTerminalSemantic
natTerminalCut = minimalCutFor natBeforeTerminalSemantic

natTerminalProofOnlyAfterPrerequisites :
  firstResidual natTerminalCut ≡ missingSemanticCorrespondence
natTerminalProofOnlyAfterPrerequisites = refl

------------------------------------------------------------------------
-- Least-privilege theorem admission is downstream of prerequisite closure.
------------------------------------------------------------------------

data TerminalSemanticProofAdmissible : BundleObligationStatus → Set where
  terminal-proof-admissible :
    TerminalSemanticProofAdmissible
      (bundle-obligation-status true true true true true false)

terminalSemanticAdmission :
  TerminalSemanticProofAdmissible natBeforeTerminalSemantic →
  ProofSearch.LiveProofSearch
terminalSemanticAdmission terminal-proof-admissible =
  ProofSearch.elaborateRoute Search.semanticCorrespondenceAdmission

sourceMissingCannotConstructTerminalAdmission :
  TerminalSemanticProofAdmissible natCurrentPrerequisites → ⊥
sourceMissingCannotConstructTerminalAdmission ()

------------------------------------------------------------------------
-- Cross-weld with the generic first-residual / producer discipline.
------------------------------------------------------------------------

sourceGapPromotionAnalogue : Promotion.PromotionStatus
sourceGapPromotionAnalogue = Promotion.promotion-status true false false false

sourceGapGenericResidualIsCorrespondence :
  Promotion.firstPromotionResidual sourceGapPromotionAnalogue
  ≡ Promotion.missingCorrespondence
sourceGapGenericResidualIsCorrespondence = refl

sourceGapGenericProducerIsCorrespondence :
  Promotion.firstResidualSelectsProducer sourceGapPromotionAnalogue
  ≡ Promotion.establishCorrespondence
sourceGapGenericProducerIsCorrespondence = refl

-- The generic promotion surface only says correspondence is missing.  The
-- bundle DAG refines that residual into its statement-specific prerequisites.
-- This is refinement, not replacement of the generic owner.

------------------------------------------------------------------------
-- Historical snapshot: later prerequisite payment changes the later cut but
-- does not rewrite the earlier fact that source support was first missing.
------------------------------------------------------------------------

record TimedPrerequisiteSnapshot : Set where
  constructor timed-prerequisite-snapshot
  field
    time : Temporal.Time
    status : BundleObligationStatus
    cut : MinimalOpenPrerequisiteCut status
    snapshotReference : String
open TimedPrerequisiteSnapshot public

earlierNatSnapshot : TimedPrerequisiteSnapshot
earlierNatSnapshot =
  timed-prerequisite-snapshot Temporal.earlier natCurrentPrerequisites natCurrentCut
    "earlier Nat prerequisite snapshot: source support first missing"

laterNatSnapshot : TimedPrerequisiteSnapshot
laterNatSnapshot =
  timed-prerequisite-snapshot Temporal.later natAfterSourceSupport natAfterSourceCut
    "later Nat prerequisite snapshot: source support paid; qualifier transport first missing"

earlierNatFirstFailurePersistsAsHistoricalFact :
  firstResidual (cut earlierNatSnapshot) ≡ missingSourceSupport
earlierNatFirstFailurePersistsAsHistoricalFact = refl

laterNatFirstFailureAdvances :
  firstResidual (cut laterNatSnapshot) ≡ missingQualifierTransport
laterNatFirstFailureAdvances = refl

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data TerminalTheoremMayLeapfrogMissingPrerequisite : Set where
data ProducerNamePaysPrerequisite : Set where
data HistoricalLaterReceiptBackfillsEarlierPayment : Set where
data ProofResponsibilityMeansBlame : Set where
data GenericLegalMinimalCutEqualsBundleProofCut : Set where

terminalTheoremCannotLeapfrogMissingPrerequisite :
  TerminalTheoremMayLeapfrogMissingPrerequisite → ⊥
terminalTheoremCannotLeapfrogMissingPrerequisite ()

producerNameDoesNotPayPrerequisite : ProducerNamePaysPrerequisite → ⊥
producerNameDoesNotPayPrerequisite ()

laterReceiptDoesNotBackfillEarlierPayment :
  HistoricalLaterReceiptBackfillsEarlierPayment → ⊥
laterReceiptDoesNotBackfillEarlierPayment ()

proofResponsibilityDoesNotMeanBlame : ProofResponsibilityMeansBlame → ⊥
proofResponsibilityDoesNotMeanBlame ()

legalMinimalCutDoesNotCollapseToBundleProofCut :
  GenericLegalMinimalCutEqualsBundleProofCut → ⊥
legalMinimalCutDoesNotCollapseToBundleProofCut ()

record StatementBundlePrerequisiteDAGBoundary : Set where
  constructor statement-bundle-prerequisite-dag-boundary
  field
    terminalSemanticTheoremHasExplicitPrerequisites : Bool
    firstMissingPrerequisiteSelectsWorkProducer : Bool
    producerNamePaysReceipt : Bool
    theoremMayLeapfrogMissingEvidence : Bool
    laterReceiptRewritesEarlierFirstFailure : Bool
    legalAuthorityCutAndProofPrerequisiteCutAreSameType : Bool

canonicalStatementBundlePrerequisiteDAGBoundary :
  StatementBundlePrerequisiteDAGBoundary
canonicalStatementBundlePrerequisiteDAGBoundary =
  statement-bundle-prerequisite-dag-boundary true true false false false false
