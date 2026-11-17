module DASHI.Cognition.ConsciousRealismDMTSourceWorldExact where

-- Source-specific instance of EXISTING acquisition/reopening and attribution
-- machinery. It does not assert unavailable FD measurements or licensed reuse.
-- Main empirical root: Timmermann et al. (PNAS 2023),
-- DOI 10.1073/pnas.2218949120. Source-written, not kernel-certified here.

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquire
import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Core.CostedResidualInformationChoiceExact as Residual
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

primaryPNAS : Attribution.AttributedSource
primaryPNAS = Attribution.mkDOISource
  "Christopher Timmermann; Leor Roseman; Sharad Haridas; Fernando E. Rosas et al."
  "Human brain effects of DMT assessed via EEG-fMRI"
  "PNAS 120(13), e2218949120"
  "2023"
  "10.1073/pnas.2218949120"
  "https://doi.org/10.1073/pnas.2218949120"
  Attribution.academicArticleSource
  "Original study source, not an independently reproduced neuroimaging result"
  Attribution.publicAttribution

-- Separate original author-written code object. It is not a second human
-- cohort or a proof that the script generated the published n=16 statistic.
primaryStaticGFCCode : Attribution.AttributedSource
primaryStaticGFCCode = Attribution.mkNoDOISource
  "Christopher Timmermann"
  "StaticGFC.m: group-level functional connectivity code"
  "timmer500/DMT_Imaging, blob f87d99f448848c3b0531fea0780ee241ebd77549"
  "2022"
  "https://github.com/timmer500/DMT_Imaging/blob/b35701d88d904e2f602164ff2eae0fc879772078/Scripts/StaticGFC.m"
  (Attribution.namedSourceKind "primary analysis code, shared 2023 DMT experimental root")
  "20 original pseudonymous source-coordinate IDs only; not n=16 eligibility or a licensed dataset"
  Attribution.publicAttribution

sourceCodeObservationArtifact : Source.SourceArtifact
sourceCodeObservationArtifact = Source.sourceArtifact
  "DMT2023:StaticGFC:author-pseudonym-list"
  Source.documentaryArtifact
  "Git blob f87d99f448848c3b0531fea0780ee241ebd77549"
  "timmer500/DMT_Imaging commit b35701d88d904e2f602164ff2eae0fc879772078"

primarySourceSnowball : Snowball.SourceRoleSnowballReceipt primaryPNAS
primarySourceSnowball = Snowball.canonicalSourceRoleSnowballReceipt primaryPNAS

originalMotionTarget : Acquire.AcquisitionTarget
originalMotionTarget = Acquire.acquisition-target
  "2023 original DMT fMRI motion/QC table"
  "Original author-linked per-subject FD series, bolus timestamps, 8-min and 28-min exclusions"
  "Original study supplementary assets / exact upstream source record"
  "Primary study data custodian, subject to independent authority and access"
  "doi:10.1073/pnas.2218949120; no email or personal identifiers"

rightsScopeTarget : Acquire.AcquisitionTarget
rightsScopeTarget = Acquire.acquisition-target
  "2023 DMT human data rights/consent scope"
  "Permissions for local scientific use, derivative statistics and redistributing data"
  "Original paper statement, source-repository licensing, institutional consent/rights"
  "Targeted author or institutional documentation only if independently approved"
  "A public Git checkout is not a licence for unrestricted redistribution"

sandersPhaseTarget : Acquire.AcquisitionTarget
sandersPhaseTarget = Acquire.acquisition-target
  "2026 DMT perceived-presence phase matrices"
  "Twenty-one complete phase matrices, 125-category codebook and cohort overlap"
  "Primary publication supplementary materials and any authorised archive"
  "Request-only route, requiring separate access authority"
  "doi:10.1093/nc/niag015; no participant identities inferred"

motionNotLocated : Acquire.AcquisitionObligation originalMotionTarget
motionNotLocated = Acquire.obligationFromNotLocated originalMotionTarget

rightsNotLocated : Acquire.AcquisitionObligation rightsScopeTarget
rightsNotLocated = Acquire.obligationFromNotLocated rightsScopeTarget

phaseNotLocated : Acquire.AcquisitionObligation sandersPhaseTarget
phaseNotLocated = Acquire.obligationFromNotLocated sandersPhaseTarget

motionBranchOpen :
  Acquire.branchState (Acquire.status motionNotLocated) ≡ Acquire.acquisitionOpen
motionBranchOpen = refl

rightsBranchOpen :
  Acquire.branchState (Acquire.status rightsNotLocated) ≡ Acquire.acquisitionOpen
rightsBranchOpen = refl

phaseBranchOpen :
  Acquire.branchState (Acquire.status phaseNotLocated) ≡ Acquire.acquisitionOpen
phaseBranchOpen = refl

-- 'notLocated' is an audit state for this precise record, NOT evidence that
-- such a record does not exist or that the original experiment was incorrect.
motionUnlocatedIsNotKnownAbsent :
  Acquire.status motionNotLocated ≡ Evidence.knownAbsent → ⊥
motionUnlocatedIsNotKnownAbsent =
  Acquire.knownAbsentCannotCarryOpenObligation motionNotLocated

-- One source object can be required by several consumers without granting
-- automatic consumer closure. These are dependency edges, not outcomes.

data DMTWorldNode : Set where
  motionQC : DMTWorldNode
  rightsScope : DMTWorldNode
  sourceLocalCopy : DMTWorldNode
  phaseMatrices : DMTWorldNode
  originalStaticCohort : DMTWorldNode
  originalDynamicCohort : DMTWorldNode
  originalJointCohort : DMTWorldNode
  staticGFCReproduction : DMTWorldNode
  temporalPresencePrediction : DMTWorldNode
  externalConsciousAgent : DMTWorldNode

data Depends : DMTWorldNode → DMTWorldNode → Set where
  motionToStatic : Depends motionQC originalStaticCohort
  motionToDynamic : Depends motionQC originalDynamicCohort
  motionToJoint : Depends motionQC originalJointCohort
  motionToReplay : Depends motionQC staticGFCReproduction
  rightsToLocalCopy : Depends rightsScope sourceLocalCopy
  rightsToReplay : Depends rightsScope staticGFCReproduction
  localCopyToReplay : Depends sourceLocalCopy staticGFCReproduction
  phaseToPresence : Depends phaseMatrices temporalPresencePrediction

sourceWorldDependencies : Acquire.AcquisitionDependencyGraph DMTWorldNode
sourceWorldDependencies = Acquire.acquisition-dependency-graph
  Depends
  "Docs/receipts/DMT2023SourceWorld.json; source-specific consumer dependencies"

qcSelectivelyReopensStatic :
  Acquire.SelectiveAcquisitionReopening
    sourceWorldDependencies motionQC originalStaticCohort
qcSelectivelyReopensStatic = Acquire.oneEdgeAcquisitionReopening motionToStatic

qcSelectivelyReopensDynamic :
  Acquire.SelectiveAcquisitionReopening
    sourceWorldDependencies motionQC originalDynamicCohort
qcSelectivelyReopensDynamic = Acquire.oneEdgeAcquisitionReopening motionToDynamic

qcSelectivelyReopensJoint :
  Acquire.SelectiveAcquisitionReopening
    sourceWorldDependencies motionQC originalJointCohort
qcSelectivelyReopensJoint = Acquire.oneEdgeAcquisitionReopening motionToJoint

rightsSelectivelyReopenStaticReplay :
  Acquire.SelectiveAcquisitionReopening
    sourceWorldDependencies rightsScope staticGFCReproduction
rightsSelectivelyReopenStaticReplay = Acquire.oneEdgeAcquisitionReopening rightsToReplay

phaseSelectivelyReopensPresencePrediction :
  Acquire.SelectiveAcquisitionReopening
    sourceWorldDependencies phaseMatrices temporalPresencePrediction
phaseSelectivelyReopensPresencePrediction =
  Acquire.oneEdgeAcquisitionReopening phaseToPresence

qcDoesNotDirectlyEstablishExternalAgent :
  Depends motionQC externalConsciousAgent → ⊥
qcDoesNotDirectlyEstablishExternalAgent ()

phaseMatricesDoNotDirectlyEstablishExternalAgent :
  Depends phaseMatrices externalConsciousAgent → ⊥
phaseMatricesDoNotDirectlyEstablishExternalAgent ()

-- Imported policies are authoritative; no second definition of a
-- probability, hypothesis, acquisition proof or "certified gain".
acquisitionBoundary : Acquire.AcquisitionSearchBoundary
acquisitionBoundary = Acquire.canonicalAcquisitionSearchBoundary

sourceBoundary : Source.SourceConditionedObservationBoundary
sourceBoundary = Source.canonicalSourceConditionedObservationBoundary

paretoBoundary : Residual.CostedResidualChoiceBoundary
paretoBoundary = Residual.canonicalCostedResidualChoiceBoundary
