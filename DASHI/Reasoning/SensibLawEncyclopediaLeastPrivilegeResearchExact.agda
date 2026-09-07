module DASHI.Reasoning.SensibLawEncyclopediaLeastPrivilegeResearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FormalisationCompatibilityExact as Compatibility
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Reasoning.SensibLawEncyclopediaCorpusClaimReceiptExact as Encyclopedia
import DASHI.Reasoning.SensibLawEncyclopediaAttributedSourceBridgeExact as Attribution

------------------------------------------------------------------------
-- ENCYCLOPEDIA RESEARCH AS LEAST-PRIVILEGE EPISTEMIC ACQUISITION
--
-- A corpus lookup is treated as an epistemic observation action.  The action
-- does not choose its own research goal: it consumes an already-selected
-- producer class from the existing proof-directed search ABI.  Escalation from
-- a bounded encyclopedia carrier to broader/primary/contradiction search is
-- justified only by an explicit live residual and remains non-promoting.
------------------------------------------------------------------------

data EncyclopediaAcquisitionScope : Set where
  exactPassageOnly : EncyclopediaAcquisitionScope
  sameEntrySameEdition : EncyclopediaAcquisitionScope
  sameEntryCrossEdition : EncyclopediaAcquisitionScope
  boundedCrossCorpus : EncyclopediaAcquisitionScope
  externalPrimarySource : EncyclopediaAcquisitionScope
  contradictionSearch : EncyclopediaAcquisitionScope

record EncyclopediaEpistemicAcquisitionDemand : Set where
  constructor encyclopedia-epistemic-acquisition-demand
  field
    consumerReference : String
    targetPropositionReference : String
    firstMissingProducer : Search.ProducerClass
    selectedScope : EncyclopediaAcquisitionScope
    selectedCorpusReference : String
    selectedEditionReference : String
    knownClaimReceiptReference : String
    sourceDiligenceResidualReference : String
    coverageReference : String
    temporalEnvelopeReference : String
    lessIntrusiveAlternativeAuditReference : String
    acquisitionBudgetReference : String
    demandReference : String
open EncyclopediaEpistemicAcquisitionDemand public

record EncyclopediaLeastPrivilegeAdmission
    (demand : EncyclopediaEpistemicAcquisitionDemand) : Set where
  constructor encyclopedia-least-privilege-admission
  field
    scopePaysFirstMissingProducerReference : String
    narrowerEquivalentScopeAuditedReference : String
    provenanceWillSurviveReference : String
    editionIdentityWillSurviveReference : String
    exactCarrierWillSurviveReference : String
    retrievalDoesNotPayProofGapReference : String
    downstreamAuthorityRemainsSeparateReference : String
open EncyclopediaLeastPrivilegeAdmission public

------------------------------------------------------------------------
-- Research deltas retain what was learned and what remains unresolved.
------------------------------------------------------------------------

record EncyclopediaResearchDelta : Set where
  constructor encyclopedia-research-delta
  field
    demand : EncyclopediaEpistemicAcquisitionDemand
    acquiredClaim : Encyclopedia.CorpusClaimReceipt
    attributedBinding : Attribution.EncyclopediaAttributedSourceBinding
    acquisitionReceiptReference : String
    newlyResolvedReference : String
    stillOpenReference : String
    contradictionStateReference : String
    nextProducer : Search.ProducerClass
    nextProducerReasonReference : String
open EncyclopediaResearchDelta public

------------------------------------------------------------------------
-- Lorde / methodological-tension anchor.
--
-- Formal research and retrieval may proceed while semantic exhaustiveness and
-- the methodological contest remain explicitly open.  Successful technical
-- construction is not an ethics-completion theorem.
------------------------------------------------------------------------

encyclopediaMethodologicalCompatibility : Compatibility.CompatibilityAssessment
encyclopediaMethodologicalCompatibility = Compatibility.canonicalMethodologicalTension

encyclopediaFormalWorkMayProceed :
  Compatibility.formalConstructionMayProceed encyclopediaMethodologicalCompatibility ≡ true
encyclopediaFormalWorkMayProceed = refl

encyclopediaSemanticExhaustivenessNotClaimed :
  Compatibility.semanticExhaustivenessClaimed encyclopediaMethodologicalCompatibility ≡ false
encyclopediaSemanticExhaustivenessNotClaimed = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CorpusLookupDefinesItsOwnProofObligation : Set where
data BroaderSearchIsAutomaticallyBetter : Set where
data RetrievalCreatesProofPayment : Set where
data CrossCorpusAgreementClosesContradictionSearch : Set where
data FormalSuccessResolvesMethodologicalTension : Set where

enyclopediaLookupDoesNotDefineProofObligation :
  CorpusLookupDefinesItsOwnProofObligation → ⊥
enyclopediaLookupDoesNotDefineProofObligation ()

broaderSearchDoesNotAutomaticallyImproveProof :
  BroaderSearchIsAutomaticallyBetter → ⊥
broaderSearchDoesNotAutomaticallyImproveProof ()

retrievalDoesNotCreateProofPayment : RetrievalCreatesProofPayment → ⊥
retrievalDoesNotCreateProofPayment ()

agreementDoesNotCloseDefeaterDuty :
  CrossCorpusAgreementClosesContradictionSearch → ⊥
agreementDoesNotCloseDefeaterDuty ()

formalSuccessDoesNotResolveMethodologicalTension :
  FormalSuccessResolvesMethodologicalTension → ⊥
formalSuccessDoesNotResolveMethodologicalTension ()

record EncyclopediaLeastPrivilegeResearchBoundary : Set where
  constructor encyclopedia-least-privilege-research-boundary
  field
    proofGapPrecedesCorpusSelection : Bool
    proofGapPrecedesCorpusSelectionIsTrue : proofGapPrecedesCorpusSelection ≡ true
    narrowerEquivalentAcquisitionMustBeAudited : Bool
    narrowerEquivalentAcquisitionMustBeAuditedIsTrue :
      narrowerEquivalentAcquisitionMustBeAudited ≡ true
    retrievalEqualsProofPayment : Bool
    retrievalEqualsProofPaymentIsFalse : retrievalEqualsProofPayment ≡ false
    broaderSearchAutomaticallyDominatesNarrowerSearch : Bool
    broaderSearchAutomaticallyDominatesNarrowerSearchIsFalse :
      broaderSearchAutomaticallyDominatesNarrowerSearch ≡ false
    methodologicalTensionRemainsOpenAfterFormalSuccess : Bool
    methodologicalTensionRemainsOpenAfterFormalSuccessIsTrue :
      methodologicalTensionRemainsOpenAfterFormalSuccess ≡ true

canonicalEncyclopediaLeastPrivilegeResearchBoundary :
  EncyclopediaLeastPrivilegeResearchBoundary
canonicalEncyclopediaLeastPrivilegeResearchBoundary =
  encyclopedia-least-privilege-research-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
