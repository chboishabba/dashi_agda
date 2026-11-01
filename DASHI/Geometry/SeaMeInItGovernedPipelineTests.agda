module DASHI.Geometry.SeaMeInItGovernedPipelineTests where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤)

open import DASHI.Governance.GovernedArtifactCore
open import DASHI.Geometry.SeaMeInItGovernedPipeline
open import DASHI.Geometry.SeaMeInItAuthorityInvariants

------------------------------------------------------------------------
-- Gate 0 finite witness: a warning causes local refinement abstention, the raw
-- state remains canonical, and the independent final-body decision promotes.

h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : Hash
h0 = sha256 0
h1 = sha256 1
h2 = sha256 2
h3 = sha256 3
h4 = sha256 4
h5 = sha256 5
h6 = sha256 6
h7 = sha256 7
h8 = sha256 8
h9 = sha256 9

policy : RefinementPolicy
policy = refinementPolicy h0 h1 h2 h3 1 4 5 3 h4 1 500 h5

evidence : RefinementEvidence
evidence = refinementEvidence h6 h7 8 7 1 2 1 2 0 true true

envelope0 : CandidateEnvelope BodyState RefinementPolicy RefinementEvidence Hash
envelope0 = candidateEnvelope rawImageFit refinedCandidate policy evidence h6 h7

refinementAbstains : RefinementReceipt
refinementAbstains =
  receipt envelope0 warn (lowViewDiversity ∷ []) [] abstain h5 h8

rawOutcome :
  GovernedOutcome
    BodyState RefinementPolicy RefinementEvidence Hash GateWarning GateBlocker
    rawImageFit refinedCandidate
rawOutcome =
  governedOutcome refinementAbstains rawImageFit (abstainSelected refl)

rawOutcomeIsRaw : resultState rawOutcome ≡ rawImageFit
rawOutcomeIsRaw = abstentionPreservesCanonical rawOutcome refl

rawTopologyWitness : TopologyEvidence
rawTopologyWitness = topologyEvidence 10475 20908 true true true true

refinedTopologyWitness : TopologyEvidence
refinedTopologyWitness = topologyEvidence 10475 20908 true true true true

finalEvidenceWitness : FinalExportEvidence
finalEvidenceWitness =
  finalExportEvidence rawTopologyWitness 143 20 0 0 900

bodyReceipt : BodyCarrierReceiptV2
bodyReceipt =
  bodyCarrierReceiptV2
    h0 h8 abstain h6 h7 h6 h9
    rawImageSource refl
    rawImageFit refl
    rawTopologyWitness refinedTopologyWitness finalEvidenceWitness
    warn
    (lowViewDiversity ∷ [])
    []
    promote
    []
    h9

bodyReceiptKeepsRawSource : canonicalSource bodyReceipt ≡ rawImageSource
bodyReceiptKeepsRawSource = refl

bodyReceiptPromotesIndependently : bodyDecision bodyReceipt ≡ promote
bodyReceiptPromotesIndependently = refl

warningStillRetained : retainedWarnings bodyReceipt ≡ lowViewDiversity ∷ []
warningStillRetained = refl

bodyLineageWitness : BodyCarrierLineageInvariant bodyReceipt
bodyLineageWitness = bodyCarrierLineageInvariant refl

finalBodyAuthorization : FinalArtifactAuthorization finalEvidenceWitness promote
finalBodyAuthorization = authorizeFinal refl refl refl refl

authorizedBodyReceipt : AuthorizedBodyCarrier bodyReceipt
authorizedBodyReceipt =
  authorizedBodyCarrier bodyLineageWitness finalBodyAuthorization

undersuitMayConsume : CanConsumeBody bodyReceipt undersuit
undersuitMayConsume = consumePromotedBody refl

------------------------------------------------------------------------
-- Gate 6 finite witness: A then B is linked through the materialized child.

p0 p1 p2 : PanelState
p0 = panelState h0 h1 h2 h3 h4 h5
p1 = panelState h6 h1 h2 h7 h8 h9
p2 = panelState h7 h1 h2 h8 h9 h0

panelEvidence0 panelEvidence1 : PanelEvidence
panelEvidence0 = panelEvidence true true true true true true 1 40 2
panelEvidence1 = panelEvidence true true true true true true 0 20 3

transitionA transitionB : PanelTransition
transitionA =
  searchTransition p0 reliefPath p1 panelEvidence0 h0 h6 admitToBeam abstain
transitionB =
  searchTransition p1 dartWedge p2 panelEvidence1 h6 h7 admitToBeam promote

orderedAB : OrderedMaterializedPair
orderedAB = orderedMaterializedPair transitionA transitionB refl true true

orderedABLinksActualChild :
  parentStateHash transitionB ≡ childStateHash transitionA
orderedABLinksActualChild = refl

materializedA : MaterializedPanelTransition transitionA
materializedA = materializedPanelTransition refl refl refl refl refl refl

materializedB : MaterializedPanelTransition transitionB
materializedB = materializedPanelTransition refl refl refl refl refl refl

orderedABAuthority : SequentialPairAuthority orderedAB
orderedABAuthority = sequentialPairAuthority materializedA materializedB refl refl

firstTransitionIsOnlyBeamAdmitted : BeamAdmissionWithoutPromotion transitionA
firstTransitionIsOnlyBeamAdmitted = beamAdmissionWithoutPromotion refl refl

searchPolicyWitness : BoundedSearchPolicy Hash
searchPolicyWitness = boundedSearchPolicy h0 h1 h2 2 8 h3 h4

boundedFailureWitness : BoundedNoPromotion Hash searchPolicyWitness
boundedFailureWitness = boundedNoPromotion h5 17 ⊤

boundedFailureHasWitness :
  noPromotedStateWithinDeclaredSearch boundedFailureWitness ≡ ⊤
boundedFailureHasWitness = refl

bt369Indication : BT369SerializerIndication
bt369Indication = bt369SerializerIndication true true true true true

bt369WarrantWitness : BT369Warrant bt369Indication
bt369WarrantWitness = bt369Warrant refl refl refl refl refl

v1NotSequential : gate6V1IsSequential ≡ false
v1NotSequential = refl

v1NotGlobalExhaustion : gate6V1ProvesBasisExhaustion ≡ false
v1NotGlobalExhaustion = refl

automaticBT369RemainsClosed : automaticBT369Promotion ≡ false
automaticBT369RemainsClosed = refl

boundedFailureAloneDoesNotWarrantBT369 :
  boundedSearchFailureAloneWarrantsBT369 ≡ false
boundedFailureAloneDoesNotWarrantBT369 = refl

automaticCandidateAuthorityRemainsClosed :
  automaticCandidateMutationAuthority ≡ false
automaticCandidateAuthorityRemainsClosed = refl
