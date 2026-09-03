module DASHI.Governance.AnomalousExperimentalDesignFarCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.CostedResidualInformationChoiceExact as Residual
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Governance.AnomalousExperimentParetoFibreExact as Pareto
import DASHI.Governance.AnomalousTemporalProofSearchExperimentAdmissionExact as Admission

------------------------------------------------------------------------
-- FAR CROSS-POLLINATION OF RESIDUAL SEARCH ARCHITECTURE
--
-- Laboratory replication, model-fidelity work, proof search, source recovery
-- and context/provenance audit may all target an open residual, but they are not
-- the same evidence kind and cannot silently substitute for one another.
------------------------------------------------------------------------

data ResidualResearchMove : Set where
  laboratoryReplication
  modelFidelityAudit
  formalProofSearch
  institutionalSourceRecovery
  contextProvenanceAudit
  : ResidualResearchMove

residualMoveKind : ResidualResearchMove → Residual.ResidualInformationMoveKind
residualMoveKind laboratoryReplication = Residual.replicationResidualMove
residualMoveKind modelFidelityAudit = Residual.fidelityResidualMove
residualMoveKind formalProofSearch = Residual.proofSearchResidualMove
residualMoveKind institutionalSourceRecovery = Residual.sourceRecoveryResidualMove
residualMoveKind contextProvenanceAudit = Residual.contextAuditResidualMove

laboratoryReplicationNotProofSearch :
  residualMoveKind laboratoryReplication ≡ residualMoveKind formalProofSearch → ⊥
laboratoryReplicationNotProofSearch ()

sourceRecoveryNotContextAudit :
  residualMoveKind institutionalSourceRecovery ≡ residualMoveKind contextProvenanceAudit → ⊥
sourceRecoveryNotContextAudit ()

fidelityAuditNotReplication :
  residualMoveKind modelFidelityAudit ≡ residualMoveKind laboratoryReplication → ⊥
fidelityAuditNotReplication ()

------------------------------------------------------------------------
-- Domain-specific routing examples.  These are search-role classifications,
-- not claims that the moves will succeed or that one move settles every
-- consumer attached to the phenomenon.
------------------------------------------------------------------------

data ResearchResidual : Set where
  ganzfeldReplicationResidual
  psilocybinMaskingResidual
  bemMethodResidual
  stargateArchiveResidual
  stargateContextResidual
  : ResearchResidual

candidateMoveFor : ResearchResidual → ResidualResearchMove
candidateMoveFor ganzfeldReplicationResidual = laboratoryReplication
candidateMoveFor psilocybinMaskingResidual = modelFidelityAudit
candidateMoveFor bemMethodResidual = formalProofSearch
candidateMoveFor stargateArchiveResidual = institutionalSourceRecovery
candidateMoveFor stargateContextResidual = contextProvenanceAudit

------------------------------------------------------------------------
-- Existing proof-search experiment admission remains a separate gate for
-- actual laboratory designs.
------------------------------------------------------------------------

presentimentLaboratoryRouteIsAdmitted : ProofSearch.RouteAdmission
presentimentLaboratoryRouteIsAdmitted = Admission.proofSearchAdmission Admission.presentimentRoute

paretoBoundary : Pareto.AnomalousExperimentParetoFibreBoundary
paretoBoundary = Pareto.canonicalAnomalousExperimentParetoFibreBoundary

residualBoundary : Residual.CostedResidualChoiceBoundary
residualBoundary = Residual.canonicalCostedResidualChoiceBoundary

proofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

forestBoundary : Forest.ReopenableHypothesisBoundary
forestBoundary = Forest.canonicalReopenableHypothesisBoundary

jointBoundary : Joint.JointSequentialPolicyBoundary
jointBoundary = Joint.canonicalJointSequentialPolicyBoundary

------------------------------------------------------------------------
-- Non-promotions across search/evidence kinds.
------------------------------------------------------------------------

data SourceRecoveryPromotesReplication : Set where

data ProofSearchPromotesEmpiricalMeasurement : Set where

data FidelityImprovementPromotesWorldEvidence : Set where

data ContextAuditPromotesMechanismProof : Set where

data ParetoPreferencePromotesTruth : Set where

data ResidualProgressPromotesConsumerClosure : Set where

sourceRecoveryDoesNotPromoteReplication : SourceRecoveryPromotesReplication → ⊥
sourceRecoveryDoesNotPromoteReplication ()

proofSearchDoesNotPromoteEmpiricalMeasurement : ProofSearchPromotesEmpiricalMeasurement → ⊥
proofSearchDoesNotPromoteEmpiricalMeasurement ()

fidelityImprovementDoesNotPromoteWorldEvidence : FidelityImprovementPromotesWorldEvidence → ⊥
fidelityImprovementDoesNotPromoteWorldEvidence ()

contextAuditDoesNotPromoteMechanismProof : ContextAuditPromotesMechanismProof → ⊥
contextAuditDoesNotPromoteMechanismProof ()

paretoPreferenceDoesNotPromoteTruth : ParetoPreferencePromotesTruth → ⊥
paretoPreferenceDoesNotPromoteTruth ()

residualProgressDoesNotPromoteConsumerClosure : ResidualProgressPromotesConsumerClosure → ⊥
residualProgressDoesNotPromoteConsumerClosure ()

record AnomalousExperimentalDesignFarCrossPollinationBoundary : Set where
  constructor anomalousExperimentalDesignFarCrossPollinationBoundary
  field
    heterogeneousMovesCanShareResidualObjective : Bool
    heterogeneousMovesCanShareResidualObjectiveIsTrue :
      heterogeneousMovesCanShareResidualObjective ≡ true
    sharedResidualObjectiveIdentifiesEvidenceKinds : Bool
    sharedResidualObjectiveIdentifiesEvidenceKindsIsFalse :
      sharedResidualObjectiveIdentifiesEvidenceKinds ≡ false
    sourceRecoveryEqualsReplication : Bool
    sourceRecoveryEqualsReplicationIsFalse : sourceRecoveryEqualsReplication ≡ false
    fidelityImprovementCreatesWorldEvidence : Bool
    fidelityImprovementCreatesWorldEvidenceIsFalse :
      fidelityImprovementCreatesWorldEvidence ≡ false
    paretoPreferenceCreatesTruth : Bool
    paretoPreferenceCreatesTruthIsFalse : paretoPreferenceCreatesTruth ≡ false
    residualProgressAutomaticallyClosesConsumer : Bool
    residualProgressAutomaticallyClosesConsumerIsFalse :
      residualProgressAutomaticallyClosesConsumer ≡ false

canonicalAnomalousExperimentalDesignFarCrossPollinationBoundary :
  AnomalousExperimentalDesignFarCrossPollinationBoundary
canonicalAnomalousExperimentalDesignFarCrossPollinationBoundary =
  anomalousExperimentalDesignFarCrossPollinationBoundary
    true refl false refl false refl false refl false refl false refl
