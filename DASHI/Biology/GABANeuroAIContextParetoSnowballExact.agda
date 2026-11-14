module DASHI.Biology.GABANeuroAIContextParetoSnowballExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.GABANeuroAIContextSnowballExact as NeuroAI
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

------------------------------------------------------------------------
-- QUALITATIVE ACQUISITION PARETO / SNOWBALL FRONTIER
--
-- We reuse the repo's recursive Pareto compatibility contract but deliberately
-- do not invent numeric costs/effect sizes for scientific acquisitions.  The
-- current frontier records only status, discovery route, authority ceiling and
-- next evidence shape.  Numeric ranking can be added only from measured costs.
------------------------------------------------------------------------

data AcquisitionStatus : Set where
  paidAndWelded : AcquisitionStatus
  boundedEvidenceOnly : AcquisitionStatus
  experimentRequired : AcquisitionStatus
  sourceAcquisitionRequired : AcquisitionStatus
  unresolvedTransfer : AcquisitionStatus

data AuthorityCeiling : Set where
  theoremOwnerCeiling : AuthorityCeiling
  sourceBoundAssociationCeiling : AuthorityCeiling
  companyReportCeiling : AuthorityCeiling
  proposalOnlyCeiling : AuthorityCeiling
  noPromotionCeiling : AuthorityCeiling

record AcquisitionNode : Set where
  constructor acquisition-node
  field
    label : String
    status : AcquisitionStatus
    discoveryRoute : Snowball.DiscoveryRoute
    authorityCeiling : AuthorityCeiling
    paidReference : String
    residualOrNextEvidenceShape : String
    feedsFutureLens : Bool
    feedsFutureLensIsTrue : feedsFutureLens ≡ true

open AcquisitionNode public

metaNeuroAIAcquisition : AcquisitionNode
metaNeuroAIAcquisition =
  acquisition-node
    "Meta NeuroAI predictive/decoding infrastructure"
    paidAndWelded
    Snowball.externalKnowledgeComparison
    sourceBoundAssociationCeiling
    "TRIBE v2 + Brain2Qwerty v2 + NeuralSet + NeuralBench receipts, attached to FMRIConnectomeProxyGovernance"
    "Next alpha: benchmark generalization across modality, task, subject and naturalistic stimulus while retaining reverse-inference and mind-reading boundaries."
    true refl

neuroforecastingAcquisition : AcquisitionNode
neuroforecastingAcquisition =
  acquisition-node
    "independent fMRI neuroforecasting of population sharing"
    paidAndWelded
    Snowball.externalKnowledgeComparison
    sourceBoundAssociationCeiling
    "Scholz 2017 plus Chan 2023 preregistered cross-cultural generalization"
    "Next alpha: held-out stimulus families, dynamic video/content classes, explicit baseline/self-report comparator and external population outcome."
    true refl

neuralinkCalibrationAcquisition : AcquisitionNode
neuralinkCalibrationAcquisition =
  acquisition-node
    "Neuralink self-supervised longitudinal decoder stabilization"
    boundedEvidenceOnly
    Snowball.residualObservation
    companyReportCeiling
    "October 2026 company update: >50,000 hours unlabeled neural data, participant-specific pretraining, weeks-without-recalibration report; exact weekly-burden figures separately secondary-reported"
    "Next alpha: independently replicated calibration-time distribution, per-participant durability curve, decoder drift metric, and cross-participant transfer benchmark."
    true refl

crossParticipantDecoderTransferAcquisition : AcquisitionNode
crossParticipantDecoderTransferAcquisition =
  acquisition-node
    "cross-participant BCI decoder transfer"
    unresolvedTransfer
    Snowball.experimentalDesign
    proposalOnlyCeiling
    "Current Neuralink live results are participant-specific; pooled/cross-participant superiority is not established in the acquired evidence."
    "Prospective held-out-participant transfer test with frozen encoder/decoder, matched calibration budget and longitudinal degradation endpoint."
    true refl

peripheralCentralTransportAcquisition : AcquisitionNode
peripheralCentralTransportAcquisition =
  acquisition-node
    "peripheral-to-central neurochemical transport"
    experimentRequired
    Snowball.experimentalDesign
    proposalOnlyCeiling
    "GABA ADHD atlas contains peripheral serum and brain-MRS rows that are intentionally non-collapsed."
    "Paired central/peripheral measurements or a validated PK/transport/biological model with timing, exposure, assay, compartment and population controls."
    true refl

dyadicObserverAcquisition : AcquisitionNode
dyadicObserverAcquisition =
  acquisition-node
    "dyadic synchrony with observer plurality"
    paidAndWelded
    Snowball.affectedSubjectVoice
    sourceBoundAssociationCeiling
    "Nguyen synchrony/attachment receipt welded to Alice Brown adult-observation != child-experience and capability/agency boundaries."
    "Next alpha: dyad-indexed participant-specific reports and neural/behavioral synchrony measures without replacing either participant's situated evidence."
    true refl

levinMultiscaleAcquisition : AcquisitionNode
levinMultiscaleAcquisition =
  acquisition-node
    "multiscale bioelectric context"
    paidAndWelded
    Snowball.externalKnowledgeComparison
    theoremOwnerCeiling
    "Existing Levin SI bioelectric-network owner reused as a multiscale signal/control anchor."
    "Next alpha: only add a CNS-specific bridge where a selected consumer requires it; do not identify organismal bioelectric control with neural decoding."
    true refl

canonicalAcquisitionFrontier : List AcquisitionNode
canonicalAcquisitionFrontier =
  metaNeuroAIAcquisition ∷
  neuroforecastingAcquisition ∷
  neuralinkCalibrationAcquisition ∷
  crossParticipantDecoderTransferAcquisition ∷
  peripheralCentralTransportAcquisition ∷
  dyadicObserverAcquisition ∷
  levinMultiscaleAcquisition ∷ []

record AcquisitionParetoBoundary : Set where
  constructor acquisition-pareto-boundary
  field
    paretoCompatibility : Pareto.RecursiveParetoCompatibility
    snowballPolicy : Snowball.DiscoveryAdmissionPolicy
    frontier : List AcquisitionNode
    numericScientificRankingInvented : Bool
    numericScientificRankingInventedIsFalse :
      numericScientificRankingInvented ≡ false
    discoveryDoesNotEqualAdmission : Bool
    discoveryDoesNotEqualAdmissionIsTrue : discoveryDoesNotEqualAdmission ≡ true
    experimentPlanDoesNotCreateEvidence : Bool
    experimentPlanDoesNotCreateEvidenceIsTrue :
      experimentPlanDoesNotCreateEvidence ≡ true
    authorityCeilingRetainedPerNode : Bool
    authorityCeilingRetainedPerNodeIsTrue :
      authorityCeilingRetainedPerNode ≡ true

open AcquisitionParetoBoundary public

canonicalAcquisitionParetoBoundary : AcquisitionParetoBoundary
canonicalAcquisitionParetoBoundary =
  acquisition-pareto-boundary
    Pareto.canonicalRecursiveParetoCompatibility
    Snowball.canonicalDiscoveryAdmissionPolicy
    canonicalAcquisitionFrontier
    false refl true refl true refl true refl

record GABANeuroAIParetoSnowballBoundary : Set where
  constructor gaba-neuro-ai-pareto-snowball-boundary
  field
    paidNodesRemainSourceOrTheoremBound : Bool
    paidNodesRemainSourceOrTheoremBoundIsTrue :
      paidNodesRemainSourceOrTheoremBound ≡ true
    companyEvidenceStaysCompanyEvidence : Bool
    companyEvidenceStaysCompanyEvidenceIsTrue :
      companyEvidenceStaysCompanyEvidence ≡ true
    unresolvedTransportRoutesToExperiment : Bool
    unresolvedTransportRoutesToExperimentIsTrue :
      unresolvedTransportRoutesToExperiment ≡ true
    crossParticipantTransferRemainsOpen : Bool
    crossParticipantTransferRemainsOpenIsTrue :
      crossParticipantTransferRemainsOpen ≡ true
    observerPluralityRetained : Bool
    observerPluralityRetainedIsTrue : observerPluralityRetained ≡ true
    futureLensMaySnowball : Bool
    futureLensMaySnowballIsTrue : futureLensMaySnowball ≡ true

canonicalGABANeuroAIParetoSnowballBoundary : GABANeuroAIParetoSnowballBoundary
canonicalGABANeuroAIParetoSnowballBoundary =
  gaba-neuro-ai-pareto-snowball-boundary
    true refl true refl true refl true refl true refl true refl
