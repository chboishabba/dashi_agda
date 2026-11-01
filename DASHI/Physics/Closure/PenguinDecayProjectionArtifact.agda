module DASHI.Physics.Closure.PenguinDecayProjectionArtifact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Sum.Base using (_⊎_; inj₁)

import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Penguin
import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayWilsonCoefficientAuthority as Wilson

------------------------------------------------------------------------
-- Rare-penguin projection artifact request/diagnostic.
--
-- This module records the finite artifact envelope needed before a penguin
-- empirical-lane projection can be interpreted: selected observable, accepted
-- SM-baseline identity, DASHI projection-defect receipt, frozen projection
-- code identity, and residual-vector artifact identity.  It is deliberately
-- non-promoting: no residual value, no fit, no new-physics claim, and no
-- empirical adequacy receipt are constructed here.

data PenguinProjectionArtifactStatus : Set where
  diagnosticEnvelopeOnlyAwaitingDigestBoundProviderArtifacts :
    PenguinProjectionArtifactStatus
  failClosedAwaitingCompleteFreezeHashPreRegistrationTuple :
    PenguinProjectionArtifactStatus

data PenguinProjectionArtifactField : Set where
  fieldSelectedDecay :
    PenguinProjectionArtifactField
  fieldSelectedObservable :
    PenguinProjectionArtifactField
  fieldProjectionDefectReceipt :
    PenguinProjectionArtifactField
  fieldInputDatasetDigest :
    PenguinProjectionArtifactField
  fieldHEPDataRecordTableChecksum :
    PenguinProjectionArtifactField
  fieldSMBaselineDigest :
    PenguinProjectionArtifactField
  fieldFlavioProviderVersionDigest :
    PenguinProjectionArtifactField
  fieldWilsonCoefficientAuthorityDigest :
    PenguinProjectionArtifactField
  fieldProjectionCodeFreezeHash :
    PenguinProjectionArtifactField
  fieldFreezeHashPreRegistrationTuple :
    PenguinProjectionArtifactField
  fieldAuthorityPopulationGate :
    PenguinProjectionArtifactField
  fieldNoPosteriorTuningAttestation :
    PenguinProjectionArtifactField
  fieldResidualVectorArtifact :
    PenguinProjectionArtifactField
  fieldResidualVectorDigest :
    PenguinProjectionArtifactField
  fieldArtifactDigest :
    PenguinProjectionArtifactField
  fieldProvenance :
    PenguinProjectionArtifactField
  fieldNonPromotionBoundary :
    PenguinProjectionArtifactField

canonicalPenguinProjectionArtifactFields :
  List PenguinProjectionArtifactField
canonicalPenguinProjectionArtifactFields =
  fieldSelectedDecay
  ∷ fieldSelectedObservable
  ∷ fieldProjectionDefectReceipt
  ∷ fieldInputDatasetDigest
  ∷ fieldHEPDataRecordTableChecksum
  ∷ fieldSMBaselineDigest
  ∷ fieldFlavioProviderVersionDigest
  ∷ fieldWilsonCoefficientAuthorityDigest
  ∷ fieldProjectionCodeFreezeHash
  ∷ fieldFreezeHashPreRegistrationTuple
  ∷ fieldAuthorityPopulationGate
  ∷ fieldNoPosteriorTuningAttestation
  ∷ fieldResidualVectorArtifact
  ∷ fieldResidualVectorDigest
  ∷ fieldArtifactDigest
  ∷ fieldProvenance
  ∷ fieldNonPromotionBoundary
  ∷ []

data PenguinDigestRole : Set where
  inputDatasetDigest :
    PenguinDigestRole
  smBaselineDigest :
    PenguinDigestRole
  wilsonCoefficientAuthorityDigest :
    PenguinDigestRole
  projectionCodeFreezeHash :
    PenguinDigestRole
  residualVectorDigest :
    PenguinDigestRole
  projectionArtifactDigest :
    PenguinDigestRole

canonicalPenguinDigestRoles :
  List PenguinDigestRole
canonicalPenguinDigestRoles =
  inputDatasetDigest
  ∷ smBaselineDigest
  ∷ wilsonCoefficientAuthorityDigest
  ∷ projectionCodeFreezeHash
  ∷ residualVectorDigest
  ∷ projectionArtifactDigest
  ∷ []

data PenguinPreRegistrationTupleField : Set where
  tupleSelectedDatasetArtifact :
    PenguinPreRegistrationTupleField
  tupleDatasetAuthorityBinding :
    PenguinPreRegistrationTupleField
  tupleDatasetDigest :
    PenguinPreRegistrationTupleField
  tupleHEPDataRecordIdentity :
    PenguinPreRegistrationTupleField
  tupleHEPDataValueTableChecksum :
    PenguinPreRegistrationTupleField
  tupleHEPDataCovarianceTableChecksum :
    PenguinPreRegistrationTupleField
  tupleSMBaselineAuthority :
    PenguinPreRegistrationTupleField
  tupleFlavioProviderVersionDigest :
    PenguinPreRegistrationTupleField
  tupleWilsonCoefficientAuthority :
    PenguinPreRegistrationTupleField
  tupleCKMSourceCommit :
    PenguinPreRegistrationTupleField
  tupleProjectionCodeFreezeHash :
    PenguinPreRegistrationTupleField
  tupleNoPosteriorTuningAttestation :
    PenguinPreRegistrationTupleField

canonicalPenguinPreRegistrationTupleFields :
  List PenguinPreRegistrationTupleField
canonicalPenguinPreRegistrationTupleFields =
  tupleSelectedDatasetArtifact
  ∷ tupleDatasetAuthorityBinding
  ∷ tupleDatasetDigest
  ∷ tupleHEPDataRecordIdentity
  ∷ tupleHEPDataValueTableChecksum
  ∷ tupleHEPDataCovarianceTableChecksum
  ∷ tupleSMBaselineAuthority
  ∷ tupleFlavioProviderVersionDigest
  ∷ tupleWilsonCoefficientAuthority
  ∷ tupleCKMSourceCommit
  ∷ tupleProjectionCodeFreezeHash
  ∷ tupleNoPosteriorTuningAttestation
  ∷ []

data PenguinFreezeAuthorityPopulationGap : Set where
  missingDatasetAuthorityDigestTuple :
    PenguinFreezeAuthorityPopulationGap
  missingHEPDataRecordTableChecksumTuple :
    PenguinFreezeAuthorityPopulationGap
  missingSMBaselineAuthorityDigestTuple :
    PenguinFreezeAuthorityPopulationGap
  missingFlavioProviderVersionDigestTuple :
    PenguinFreezeAuthorityPopulationGap
  missingWilsonCoefficientAuthorityDigestTuple :
    PenguinFreezeAuthorityPopulationGap
  missingCKMSourceCommitAuthority :
    PenguinFreezeAuthorityPopulationGap
  missingProjectionCodeFreezeHash :
    PenguinFreezeAuthorityPopulationGap
  missingNoPosteriorTuningAttestation :
    PenguinFreezeAuthorityPopulationGap

canonicalPenguinFreezeAuthorityPopulationGaps :
  List PenguinFreezeAuthorityPopulationGap
canonicalPenguinFreezeAuthorityPopulationGaps =
  missingDatasetAuthorityDigestTuple
  ∷ missingHEPDataRecordTableChecksumTuple
  ∷ missingSMBaselineAuthorityDigestTuple
  ∷ missingFlavioProviderVersionDigestTuple
  ∷ missingWilsonCoefficientAuthorityDigestTuple
  ∷ missingCKMSourceCommitAuthority
  ∷ missingProjectionCodeFreezeHash
  ∷ missingNoPosteriorTuningAttestation
  ∷ []

data CKMSourceCommitMissingAuthority : Set where
  missingCKMCarrierCommitHash :
    CKMSourceCommitMissingAuthority
  missingCKMCarrierSourceAuthority :
    CKMSourceCommitMissingAuthority
  missingVtbVtsStarLoopFactorBinding :
    CKMSourceCommitMissingAuthority

canonicalCKMSourceCommitMissingAuthorities :
  List CKMSourceCommitMissingAuthority
canonicalCKMSourceCommitMissingAuthorities =
  missingCKMCarrierCommitHash
  ∷ missingCKMCarrierSourceAuthority
  ∷ missingVtbVtsStarLoopFactorBinding
  ∷ []

record CKMSourceCommitFreezeSlot : Set where
  constructor mkCKMSourceCommitFreezeSlot
  field
    commitOrRevision :
      String

    commitOrRevisionIsRequired :
      commitOrRevision
      ≡
      "required: CKM carrier source commit or immutable external source revision"

    authorityBinding :
      String

    authorityBindingIsRequired :
      authorityBinding
      ≡
      "required: authority binding for Vtb Vts* loop-factor inputs"

    acceptedHere :
      Bool

    acceptedHereIsFalse :
      acceptedHere ≡ false

    missingAuthorities :
      List CKMSourceCommitMissingAuthority

    missingAuthoritiesAreCanonical :
      missingAuthorities
      ≡
      canonicalCKMSourceCommitMissingAuthorities

open CKMSourceCommitFreezeSlot public

canonicalCKMSourceCommitFreezeSlot :
  CKMSourceCommitFreezeSlot
canonicalCKMSourceCommitFreezeSlot =
  mkCKMSourceCommitFreezeSlot
    "required: CKM carrier source commit or immutable external source revision"
    refl
    "required: authority binding for Vtb Vts* loop-factor inputs"
    refl
    false
    refl
    canonicalCKMSourceCommitMissingAuthorities
    refl

record PenguinDigestBinding : Set where
  constructor mkPenguinDigestBinding
  field
    role :
      PenguinDigestRole

    algorithm :
      String

    digest :
      String

    boundArtifact :
      String

open PenguinDigestBinding public

record SuppliedPenguinDatasetChecksumAuthority : Set where
  constructor mkSuppliedPenguinDatasetChecksumAuthority
  field
    sourceCandidate :
      Contract.PenguinDatasetSourceCandidateName

    sourceCandidateKnown :
      sourceCandidate
      ≡
      Contract.cmsHEPData135675ResultsTable
      ⊎
      sourceCandidate
      ≡
      Contract.lhcbBsMuMuCERN5r7hzC7e34

    sourceDiscriminator :
      Contract.PenguinDatasetSourceDiscriminator

    sourceDiscriminatorIsCanonical :
      sourceDiscriminator
      ≡
      Contract.canonicalPenguinDatasetSourceDiscriminator

    digestAlgorithm :
      String

    digestAlgorithmIsSHA256 :
      digestAlgorithm ≡ "sha256"

    payloadSHA256 :
      String

    payloadSHA256Verified :
      Bool

    payloadSHA256VerifiedIsTrue :
      payloadSHA256Verified ≡ true

    authorityReceipt :
      String

    acceptedExternalAuthority :
      Bool

    acceptedExternalAuthorityIsTrue :
      acceptedExternalAuthority ≡ true

open SuppliedPenguinDatasetChecksumAuthority public

canonicalCMSResultsDatasetChecksumAuthority :
  SuppliedPenguinDatasetChecksumAuthority
canonicalCMSResultsDatasetChecksumAuthority =
  mkSuppliedPenguinDatasetChecksumAuthority
    Contract.cmsHEPData135675ResultsTable
    (inj₁ refl)
    Contract.canonicalPenguinDatasetSourceDiscriminator
    refl
    "sha256"
    refl
    "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"
    true
    refl
    "local artifact /home/c/Downloads/HEPData-ins2616304-v1-Results.yaml; HEPData ins2616304 v1 table 1435213 Results; DOI 10.17182/hepdata.135675.v1/t1"
    true
    refl

record PenguinFreezeHashPreRegistrationTuple : Set where
  constructor mkPenguinFreezeHashPreRegistrationTuple
  field
    selectedDatasetArtifact :
      String

    selectedDatasetAuthorityBinding :
      String

    selectedDatasetSourceCitation :
      String

    selectedDatasetVersionOrRecord :
      String

    datasetSourceDiscriminator :
      Contract.PenguinDatasetSourceDiscriminator

    datasetSourceDiscriminatorIsCanonical :
      datasetSourceDiscriminator
      ≡
      Contract.canonicalPenguinDatasetSourceDiscriminator

    selectedDatasetSourceCandidate :
      Contract.PenguinDatasetSourceCandidateName

    selectedDatasetSourceCandidateIsLHCb :
      selectedDatasetSourceCandidate
      ≡
      Contract.lhcbBsMuMuCERN5r7hzC7e34

    selectedDatasetDigestBinding :
      PenguinDigestBinding

    selectedDatasetDigestRoleIsInput :
      role selectedDatasetDigestBinding
      ≡
      inputDatasetDigest

    hepdataRecordId :
      String

    hepdataValueTableDOI :
      String

    hepdataValueTableChecksum :
      String

    hepdataCovarianceTableDOI :
      String

    hepdataCovarianceTableChecksum :
      String

    smBaselineAuthorityArtifact :
      String

    smBaselineAuthoritySource :
      String

    smBaselineDigestBinding :
      PenguinDigestBinding

    smBaselineDigestRoleIsSMBaseline :
      role smBaselineDigestBinding
      ≡
      smBaselineDigest

    flavioProviderVersionDigest :
      Wilson.FlavioProviderVersionDigest

    flavioProviderVersionDigestIsCanonical :
      flavioProviderVersionDigest
      ≡
      Wilson.canonicalFlavioProviderVersionDigest

    wilsonCoefficientAuthorityArtifact :
      String

    wilsonCoefficientAuthoritySource :
      String

    wilsonCoefficientScheme :
      String

    wilsonCoefficientDigestBinding :
      PenguinDigestBinding

    wilsonCoefficientDigestRoleIsWilsonAuthority :
      role wilsonCoefficientDigestBinding
      ≡
      wilsonCoefficientAuthorityDigest

    ckmSourceCommit :
      String

    ckmSourceAuthority :
      String

    ckmSourceCommitFreezeSlot :
      CKMSourceCommitFreezeSlot

    ckmSourceCommitFreezeSlotIsCanonical :
      ckmSourceCommitFreezeSlot
      ≡
      canonicalCKMSourceCommitFreezeSlot

    projectionCodeHashBinding :
      PenguinDigestBinding

    projectionCodeHashRoleIsFreezeHash :
      role projectionCodeHashBinding
      ≡
      projectionCodeFreezeHash

    noPosteriorTuningAttestation :
      String

    tupleFields :
      List PenguinPreRegistrationTupleField

    tupleFieldsAreCanonical :
      tupleFields
      ≡
      canonicalPenguinPreRegistrationTupleFields

open PenguinFreezeHashPreRegistrationTuple public

data PenguinResidualVectorArtifactRole : Set where
  residualVectorJSON :
    PenguinResidualVectorArtifactRole
  residualCovarianceOrUncertaintyEnvelope :
    PenguinResidualVectorArtifactRole
  residualBinBindingManifest :
    PenguinResidualVectorArtifactRole

canonicalPenguinResidualVectorArtifactRoles :
  List PenguinResidualVectorArtifactRole
canonicalPenguinResidualVectorArtifactRoles =
  residualVectorJSON
  ∷ residualCovarianceOrUncertaintyEnvelope
  ∷ residualBinBindingManifest
  ∷ []

record PenguinResidualVectorArtifact : Set where
  constructor mkPenguinResidualVectorArtifact
  field
    artifactPath :
      String

    artifactRole :
      PenguinResidualVectorArtifactRole

    vectorDigest :
      PenguinDigestBinding

    vectorDigestRoleIsResidual :
      role vectorDigest
      ≡
      residualVectorDigest

open PenguinResidualVectorArtifact public

data PenguinProjectionProvenanceStep : Set where
  selectedRarePenguinObservable :
    PenguinProjectionProvenanceStep
  digestBoundInputDataset :
    PenguinProjectionProvenanceStep
  digestBoundSMBaseline :
    PenguinProjectionProvenanceStep
  dashIPenguinProjectionDefectReceipt :
    PenguinProjectionProvenanceStep
  frozenProjectionCodeIdentity :
    PenguinProjectionProvenanceStep
  residualVectorArtifactIdentity :
    PenguinProjectionProvenanceStep
  projectionArtifactChecksum :
    PenguinProjectionProvenanceStep
  nonPromotionDiagnosticBoundary :
    PenguinProjectionProvenanceStep

canonicalPenguinProjectionProvenance :
  List PenguinProjectionProvenanceStep
canonicalPenguinProjectionProvenance =
  selectedRarePenguinObservable
  ∷ digestBoundInputDataset
  ∷ digestBoundSMBaseline
  ∷ dashIPenguinProjectionDefectReceipt
  ∷ frozenProjectionCodeIdentity
  ∷ residualVectorArtifactIdentity
  ∷ projectionArtifactChecksum
  ∷ nonPromotionDiagnosticBoundary
  ∷ []

data PenguinProjectionArtifactBoundary : Set where
  noDatasetParsingHere :
    PenguinProjectionArtifactBoundary
  noSMBaselineComputationHere :
    PenguinProjectionArtifactBoundary
  noProjectionExecutionHere :
    PenguinProjectionArtifactBoundary
  noResidualMagnitudeClaimHere :
    PenguinProjectionArtifactBoundary
  noEmpiricalAdequacyClaimHere :
    PenguinProjectionArtifactBoundary
  noStandardModelTensionClaimHere :
    PenguinProjectionArtifactBoundary
  noNonStandardModelPromotionHere :
    PenguinProjectionArtifactBoundary

canonicalPenguinProjectionArtifactBoundaries :
  List PenguinProjectionArtifactBoundary
canonicalPenguinProjectionArtifactBoundaries =
  noDatasetParsingHere
  ∷ noSMBaselineComputationHere
  ∷ noProjectionExecutionHere
  ∷ noResidualMagnitudeClaimHere
  ∷ noEmpiricalAdequacyClaimHere
  ∷ noStandardModelTensionClaimHere
  ∷ noNonStandardModelPromotionHere
  ∷ []

data PenguinNoPosteriorTuningBlocker : Set where
  noPosteriorTuningBlockedUntilDatasetChecksumFrozen :
    PenguinNoPosteriorTuningBlocker
  noPosteriorTuningBlockedUntilSMBaselineDigestFrozen :
    PenguinNoPosteriorTuningBlocker
  noPosteriorTuningBlockedUntilWilsonProviderDigestFrozen :
    PenguinNoPosteriorTuningBlocker
  noPosteriorTuningBlockedUntilCKMCommitFrozen :
    PenguinNoPosteriorTuningBlocker
  noPosteriorTuningBlockedUntilProjectionCodeHashFrozen :
    PenguinNoPosteriorTuningBlocker
  noPosteriorTuningBlockedUntilAttestationSigned :
    PenguinNoPosteriorTuningBlocker

canonicalPenguinNoPosteriorTuningBlockers :
  List PenguinNoPosteriorTuningBlocker
canonicalPenguinNoPosteriorTuningBlockers =
  noPosteriorTuningBlockedUntilDatasetChecksumFrozen
  ∷ noPosteriorTuningBlockedUntilSMBaselineDigestFrozen
  ∷ noPosteriorTuningBlockedUntilWilsonProviderDigestFrozen
  ∷ noPosteriorTuningBlockedUntilCKMCommitFrozen
  ∷ noPosteriorTuningBlockedUntilProjectionCodeHashFrozen
  ∷ noPosteriorTuningBlockedUntilAttestationSigned
  ∷ []

data PenguinCMSChecksumReadinessBlocker : Set where
  cmsReadinessMissingFlavioProviderPackageDigest :
    PenguinCMSChecksumReadinessBlocker
  cmsReadinessMissingFlavioRuntimeEnvironmentDigest :
    PenguinCMSChecksumReadinessBlocker
  cmsReadinessMissingWilsonCoefficientAuthorityDigest :
    PenguinCMSChecksumReadinessBlocker
  cmsReadinessMissingNoPosteriorTuningAttestation :
    PenguinCMSChecksumReadinessBlocker
  cmsReadinessMissingProjectionCodeFreezeHash :
    PenguinCMSChecksumReadinessBlocker
  cmsReadinessMissingLHCbArtifactChecksumIfThreadLaneRetained :
    PenguinCMSChecksumReadinessBlocker

canonicalPenguinCMSChecksumReadinessBlockers :
  List PenguinCMSChecksumReadinessBlocker
canonicalPenguinCMSChecksumReadinessBlockers =
  cmsReadinessMissingFlavioProviderPackageDigest
  ∷ cmsReadinessMissingFlavioRuntimeEnvironmentDigest
  ∷ cmsReadinessMissingWilsonCoefficientAuthorityDigest
  ∷ cmsReadinessMissingNoPosteriorTuningAttestation
  ∷ cmsReadinessMissingProjectionCodeFreezeHash
  ∷ cmsReadinessMissingLHCbArtifactChecksumIfThreadLaneRetained
  ∷ []

data PenguinEmpiricalPromotionToken : Set where

penguinEmpiricalPromotionImpossibleHere :
  PenguinEmpiricalPromotionToken →
  ⊥
penguinEmpiricalPromotionImpossibleHere ()

record PenguinDecayProjectionArtifactRequest : Setω where
  field
    status :
      PenguinProjectionArtifactStatus

    selectedDecay :
      Penguin.RarePenguinDecay

    selectedObservable :
      Penguin.IndirectObservable

    projectionDefectReceipt :
      Penguin.PenguinDecayProjectionDefectReceipt

    projectionDefectReceiptIsCanonical :
      projectionDefectReceipt
      ≡
      Penguin.canonicalPenguinDecayProjectionDefectReceipt

    selectedWitness :
      Penguin.IndirectWitness

    selectedWitnessIsIndirect :
      Penguin.extractionMode selectedWitness
      ≡
      Penguin.indirectProjectionDefectExtraction

    selectedWitnessReturnsResidualDefect :
      Penguin.extractedDefect selectedWitness
      ≡
      Penguin.residualDefectSurface

    requiredFields :
      List PenguinProjectionArtifactField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalPenguinProjectionArtifactFields

    requiredDigestRoles :
      List PenguinDigestRole

    requiredDigestRolesAreCanonical :
      requiredDigestRoles
      ≡
      canonicalPenguinDigestRoles

    datasetSourceDiscriminator :
      Contract.PenguinDatasetSourceDiscriminator

    datasetSourceDiscriminatorIsCanonical :
      datasetSourceDiscriminator
      ≡
      Contract.canonicalPenguinDatasetSourceDiscriminator

    cmsChecksumAuthorityCandidate :
      SuppliedPenguinDatasetChecksumAuthority

    cmsChecksumAuthorityCandidateIsCanonical :
      cmsChecksumAuthorityCandidate
      ≡
      canonicalCMSResultsDatasetChecksumAuthority

    selectedThreadChecksumAuthorityPresent :
      Bool

    selectedThreadChecksumAuthorityPresentIsFalse :
      selectedThreadChecksumAuthorityPresent ≡ false

    inputDataset :
      PenguinDigestBinding

    inputDatasetDigestRoleIsInput :
      role inputDataset
      ≡
      inputDatasetDigest

    smBaseline :
      PenguinDigestBinding

    smBaselineDigestRoleIsSMBaseline :
      role smBaseline
      ≡
      smBaselineDigest

    projectionCodeFreeze :
      PenguinDigestBinding

    projectionCodeFreezeRoleIsFreezeHash :
      role projectionCodeFreeze
      ≡
      projectionCodeFreezeHash

    freezeHashPreRegistrationTuple :
      PenguinFreezeHashPreRegistrationTuple

    freezeHashPreRegistrationTupleFields :
      List PenguinPreRegistrationTupleField

    freezeHashPreRegistrationTupleFieldsAreCanonical :
      freezeHashPreRegistrationTupleFields
      ≡
      canonicalPenguinPreRegistrationTupleFields

    freezeAuthorityPopulationGaps :
      List PenguinFreezeAuthorityPopulationGap

    freezeAuthorityPopulationGapsAreCanonical :
      freezeAuthorityPopulationGaps
      ≡
      canonicalPenguinFreezeAuthorityPopulationGaps

    allFreezeAuthoritiesPopulated :
      Bool

    allFreezeAuthoritiesPopulatedIsFalse :
      allFreezeAuthoritiesPopulated
      ≡
      false

    freezeGateOpen :
      Bool

    freezeGateOpenIsFalse :
      freezeGateOpen
      ≡
      false

    posteriorTuningConstructedHere :
      Bool

    posteriorTuningConstructedHereIsFalse :
      posteriorTuningConstructedHere
      ≡
      false

    noPosteriorTuningBlockers :
      List PenguinNoPosteriorTuningBlocker

    noPosteriorTuningBlockersAreCanonical :
      noPosteriorTuningBlockers
      ≡
      canonicalPenguinNoPosteriorTuningBlockers

    residualVectorArtifact :
      PenguinResidualVectorArtifact

    residualVectorArtifactRoleIsJSON :
      artifactRole residualVectorArtifact
      ≡
      residualVectorJSON

    artifactDigest :
      PenguinDigestBinding

    artifactDigestRoleIsProjectionArtifact :
      role artifactDigest
      ≡
      projectionArtifactDigest

    residualArtifactRoles :
      List PenguinResidualVectorArtifactRole

    residualArtifactRolesAreCanonical :
      residualArtifactRoles
      ≡
      canonicalPenguinResidualVectorArtifactRoles

    provenance :
      List PenguinProjectionProvenanceStep

    provenanceIsCanonical :
      provenance
      ≡
      canonicalPenguinProjectionProvenance

    empiricalResultConstructedHere :
      Bool

    empiricalResultConstructedHereIsFalse :
      empiricalResultConstructedHere
      ≡
      false

    promotionConstructedHere :
      Bool

    promotionConstructedHereIsFalse :
      promotionConstructedHere
      ≡
      false

    nonPromotionBoundary :
      List PenguinProjectionArtifactBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalPenguinProjectionArtifactBoundaries

    providerRequestText :
      List String

    promotionTokenBlocked :
      PenguinEmpiricalPromotionToken →
      ⊥

open PenguinDecayProjectionArtifactRequest public

canonicalInputDatasetDigestBinding :
  PenguinDigestBinding
canonicalInputDatasetDigestBinding =
  mkPenguinDigestBinding
    inputDatasetDigest
    "sha256"
    "required: provider-supplied penguin input dataset digest"
    "selected rare-penguin observable dataset"

canonicalSMBaselineDigestBinding :
  PenguinDigestBinding
canonicalSMBaselineDigestBinding =
  mkPenguinDigestBinding
    smBaselineDigest
    "sha256"
    "required: provider-supplied Standard Model baseline digest"
    "frozen Standard Model penguin baseline artifact"

canonicalWilsonCoefficientAuthorityDigestBinding :
  PenguinDigestBinding
canonicalWilsonCoefficientAuthorityDigestBinding =
  mkPenguinDigestBinding
    wilsonCoefficientAuthorityDigest
    "sha256"
    "required: provider-supplied Wilson coefficient authority digest"
    "accepted Wilson coefficient scheme, values, scale law, and effective Hamiltonian convention"

canonicalProjectionCodeFreezeBinding :
  PenguinDigestBinding
canonicalProjectionCodeFreezeBinding =
  mkPenguinDigestBinding
    projectionCodeFreezeHash
    "sha256"
    "required: provider-supplied projection code freeze hash"
    "DASHI penguin projection-defect runner source tree"

canonicalFreezeHashPreRegistrationTuple :
  PenguinFreezeHashPreRegistrationTuple
canonicalFreezeHashPreRegistrationTuple =
  mkPenguinFreezeHashPreRegistrationTuple
    "none: citation-only LHCb slot has no selected machine-readable dataset artifact"
    "CitationAuthority repository.cern/records/5r7hz-c7e34; artifactAuthority=false"
    "arXiv:2108.09283; CERN-EP-2021-133; Phys.Rev.D 104 (2021) L091102; HEPData deposited=false"
    "repository.cern/records/5r7hz-c7e34"
    Contract.canonicalPenguinDatasetSourceDiscriminator
    refl
    Contract.lhcbBsMuMuCERN5r7hzC7e34
    refl
    canonicalInputDatasetDigestBinding
    refl
    "repository.cern/records/5r7hz-c7e34"
    "none: HEPData deposited=false; no machine-readable value table"
    "none: no fabricated SHA; artifactAuthority=false"
    "none: HEPData deposited=false; no covariance table"
    "none: no fabricated SHA; artifactAuthority=false"
    "required: frozen Standard Model baseline authority artifact"
    "required: accepted SM baseline source including form factors and uncertainty budget"
    canonicalSMBaselineDigestBinding
    refl
    Wilson.canonicalFlavioProviderVersionDigest
    refl
    "required: frozen Wilson coefficient authority artifact"
    "required: Wilson coefficient source, scheme, scale law, and Hamiltonian convention"
    "required: Wilson coefficient scheme identifier"
    canonicalWilsonCoefficientAuthorityDigestBinding
    refl
    "required: CKM carrier/source commit or immutable external source revision"
    "required: CKM source authority binding for loop factors"
    canonicalCKMSourceCommitFreezeSlot
    refl
    canonicalProjectionCodeFreezeBinding
    refl
    "required: provider attests no posterior tuning after observing residuals"
    canonicalPenguinPreRegistrationTupleFields
    refl

canonicalResidualVectorDigestBinding :
  PenguinDigestBinding
canonicalResidualVectorDigestBinding =
  mkPenguinDigestBinding
    residualVectorDigest
    "sha256"
    "required: provider-supplied residual vector artifact digest"
    "residual_vector.json"

canonicalResidualVectorArtifact :
  PenguinResidualVectorArtifact
canonicalResidualVectorArtifact =
  mkPenguinResidualVectorArtifact
    "required: residual_vector.json path"
    residualVectorJSON
    canonicalResidualVectorDigestBinding
    refl

canonicalProjectionArtifactDigestBinding :
  PenguinDigestBinding
canonicalProjectionArtifactDigestBinding =
  mkPenguinDigestBinding
    projectionArtifactDigest
    "sha256"
    "required: provider-supplied envelope/provenance artifact digest"
    "penguin_projection_artifact.json"

canonicalPenguinDecayProjectionArtifactRequest :
  PenguinDecayProjectionArtifactRequest
canonicalPenguinDecayProjectionArtifactRequest =
  record
    { status =
        failClosedAwaitingCompleteFreezeHashPreRegistrationTuple
    ; selectedDecay =
        Penguin.bToSLeptonPair
    ; selectedObservable =
        Penguin.angularCoefficientDeviation
    ; projectionDefectReceipt =
        Penguin.canonicalPenguinDecayProjectionDefectReceipt
    ; projectionDefectReceiptIsCanonical =
        refl
    ; selectedWitness =
        Penguin.extractIndirectWitness
          Penguin.bToSLeptonPair
          Penguin.angularCoefficientDeviation
    ; selectedWitnessIsIndirect =
        refl
    ; selectedWitnessReturnsResidualDefect =
        refl
    ; requiredFields =
        canonicalPenguinProjectionArtifactFields
    ; requiredFieldsAreCanonical =
        refl
    ; requiredDigestRoles =
        canonicalPenguinDigestRoles
    ; requiredDigestRolesAreCanonical =
        refl
    ; datasetSourceDiscriminator =
        Contract.canonicalPenguinDatasetSourceDiscriminator
    ; datasetSourceDiscriminatorIsCanonical =
        refl
    ; cmsChecksumAuthorityCandidate =
        canonicalCMSResultsDatasetChecksumAuthority
    ; cmsChecksumAuthorityCandidateIsCanonical =
        refl
    ; selectedThreadChecksumAuthorityPresent =
        false
    ; selectedThreadChecksumAuthorityPresentIsFalse =
        refl
    ; inputDataset =
        canonicalInputDatasetDigestBinding
    ; inputDatasetDigestRoleIsInput =
        refl
    ; smBaseline =
        canonicalSMBaselineDigestBinding
    ; smBaselineDigestRoleIsSMBaseline =
        refl
    ; projectionCodeFreeze =
        canonicalProjectionCodeFreezeBinding
    ; projectionCodeFreezeRoleIsFreezeHash =
        refl
    ; freezeHashPreRegistrationTuple =
        canonicalFreezeHashPreRegistrationTuple
    ; freezeHashPreRegistrationTupleFields =
        canonicalPenguinPreRegistrationTupleFields
    ; freezeHashPreRegistrationTupleFieldsAreCanonical =
        refl
    ; freezeAuthorityPopulationGaps =
        canonicalPenguinFreezeAuthorityPopulationGaps
    ; freezeAuthorityPopulationGapsAreCanonical =
        refl
    ; allFreezeAuthoritiesPopulated =
        false
    ; allFreezeAuthoritiesPopulatedIsFalse =
        refl
    ; freezeGateOpen =
        false
    ; freezeGateOpenIsFalse =
        refl
    ; posteriorTuningConstructedHere =
        false
    ; posteriorTuningConstructedHereIsFalse =
        refl
    ; noPosteriorTuningBlockers =
        canonicalPenguinNoPosteriorTuningBlockers
    ; noPosteriorTuningBlockersAreCanonical =
        refl
    ; residualVectorArtifact =
        canonicalResidualVectorArtifact
    ; residualVectorArtifactRoleIsJSON =
        refl
    ; artifactDigest =
        canonicalProjectionArtifactDigestBinding
    ; artifactDigestRoleIsProjectionArtifact =
        refl
    ; residualArtifactRoles =
        canonicalPenguinResidualVectorArtifactRoles
    ; residualArtifactRolesAreCanonical =
        refl
    ; provenance =
        canonicalPenguinProjectionProvenance
    ; provenanceIsCanonical =
        refl
    ; empiricalResultConstructedHere =
        false
    ; empiricalResultConstructedHereIsFalse =
        refl
    ; promotionConstructedHere =
        false
    ; promotionConstructedHereIsFalse =
        refl
    ; nonPromotionBoundary =
        canonicalPenguinProjectionArtifactBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; providerRequestText =
        "Bind selected decay b -> s lepton pair and angular-coefficient deviation before reading the residual vector"
        ∷ "Populate the freeze-hash pre-registration tuple before any residual comparison is unlocked"
        ∷ "Dataset-source discriminator records CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results with checksum authority, while the thread-selected LHCb record repository.cern/records/5r7hz-c7e34 is CitationAuthority only"
        ∷ "Do not promote the selected thread observable from the CMS checksum candidate; selectedThreadChecksumAuthorityPresent remains false for the LHCb-specific lane"
        ∷ "Supply inputDatasetDigest as a sha256 of the exact empirical dataset artifact, source citation, version/record id, covariance, and bin map"
        ∷ "For the selected LHCb slot, HEPData deposited=false, artifactAuthority=false, and no machine-readable table or fabricated SHA is accepted"
        ∷ "Supply smBaselineDigest as a sha256 of the frozen Standard Model baseline authority artifact"
        ∷ "Supply flavio provider version 2.7.0 package, parameter-card, and runtime environment digests"
        ∷ "Supply Wilson coefficient authority source, scheme, scale law, Hamiltonian convention, and digest"
        ∷ "Supply CKM source commit or immutable source revision for loop-factor inputs"
        ∷ "Supply projectionCodeFreezeHash as a sha256 or equivalent immutable code-freeze identity"
        ∷ "Attest that no posterior tuning was performed after residual inspection; missing dataset, SM, Wilson, CKM, code, or signed attestation blocks the bridge"
        ∷ "Fail closed: freezeGateOpen remains false until all dataset, SM, Wilson, CKM, code, and no-posterior-tuning authorities are populated"
        ∷ "Supply residual_vector.json and residualVectorDigest; this module does not read or score the vector"
        ∷ "Supply projectionArtifactDigest covering the envelope, provenance, digests, and projection-defect receipt identity"
        ∷ "No empirical result, adequacy claim, Standard-Model tension claim, or promotion is authorized by this request"
        ∷ []
    ; promotionTokenBlocked =
        penguinEmpiricalPromotionImpossibleHere
    }

canonicalPenguinProjectionArtifactHasNoResult :
  empiricalResultConstructedHere
    canonicalPenguinDecayProjectionArtifactRequest
  ≡
  false
canonicalPenguinProjectionArtifactHasNoResult =
  refl

canonicalPenguinProjectionArtifactHasNoPromotion :
  promotionConstructedHere
    canonicalPenguinDecayProjectionArtifactRequest
  ≡
  false
canonicalPenguinProjectionArtifactHasNoPromotion =
  refl

canonicalPenguinProjectionArtifactUsesResidualDefect :
  Penguin.extractedDefect
    (selectedWitness canonicalPenguinDecayProjectionArtifactRequest)
  ≡
  Penguin.residualDefectSurface
canonicalPenguinProjectionArtifactUsesResidualDefect =
  refl

canonicalPenguinProjectionArtifactFreezeStatus :
  status canonicalPenguinDecayProjectionArtifactRequest
  ≡
  failClosedAwaitingCompleteFreezeHashPreRegistrationTuple
canonicalPenguinProjectionArtifactFreezeStatus =
  refl

canonicalPenguinProjectionArtifactAuthorityPopulationGaps :
  freezeAuthorityPopulationGaps canonicalPenguinDecayProjectionArtifactRequest
  ≡
  canonicalPenguinFreezeAuthorityPopulationGaps
canonicalPenguinProjectionArtifactAuthorityPopulationGaps =
  refl

canonicalPenguinProjectionArtifactAuthoritiesNotPopulated :
  allFreezeAuthoritiesPopulated canonicalPenguinDecayProjectionArtifactRequest
  ≡
  false
canonicalPenguinProjectionArtifactAuthoritiesNotPopulated =
  refl

canonicalPenguinProjectionArtifactFreezeGateClosed :
  freezeGateOpen canonicalPenguinDecayProjectionArtifactRequest
  ≡
  false
canonicalPenguinProjectionArtifactFreezeGateClosed =
  refl

canonicalPenguinProjectionArtifactNoPosteriorTuning :
  posteriorTuningConstructedHere canonicalPenguinDecayProjectionArtifactRequest
  ≡
  false
canonicalPenguinProjectionArtifactNoPosteriorTuning =
  refl

record PenguinCMSChecksumPopulatedReadinessReceipt : Setω where
  constructor mkPenguinCMSChecksumPopulatedReadinessReceipt
  field
    readinessProjectionArtifact :
      PenguinDecayProjectionArtifactRequest

    cmsDatasetChecksumAuthority :
      SuppliedPenguinDatasetChecksumAuthority

    cmsDatasetChecksumAuthorityIsCanonical :
      cmsDatasetChecksumAuthority
      ≡
      canonicalCMSResultsDatasetChecksumAuthority

    cmsDatasetSourceCandidateIsCMS :
      sourceCandidate cmsDatasetChecksumAuthority
      ≡
      Contract.cmsHEPData135675ResultsTable

    cmsDatasetDigestAlgorithmIsSHA256 :
      digestAlgorithm cmsDatasetChecksumAuthority
      ≡
      "sha256"

    cmsDatasetPayloadSHA256IsCanonical :
      payloadSHA256 cmsDatasetChecksumAuthority
      ≡
      "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"

    cmsDatasetPayloadSHA256Verified :
      payloadSHA256Verified cmsDatasetChecksumAuthority
      ≡
      true

    cmsDatasetAuthorityPresent :
      Bool

    cmsDatasetAuthorityPresentIsTrue :
      cmsDatasetAuthorityPresent ≡ true

    cmsTableArtifact :
      Contract.CMSTableArtifactChecksumCandidate

    cmsTableArtifactIsCanonical :
      cmsTableArtifact
      ≡
      Contract.canonicalCMSTableArtifactChecksumCandidate

    cmsTableRecordIsCanonical :
      Contract.hepDataRecord cmsTableArtifact
      ≡
      "HEPData:ins2616304:v1"

    cmsTableDOIIsCanonical :
      Contract.tableDOI cmsTableArtifact
      ≡
      "10.17182/hepdata.135675.v1/t1"

    cmsTableIdentifierIsCanonical :
      Contract.tableIdentifier cmsTableArtifact
      ≡
      "1435213"

    cmsTableSHA256IsCanonical :
      Contract.sha256 cmsTableArtifact
      ≡
      "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"

    cmsTableSHA256Verified :
      Contract.sha256Verified cmsTableArtifact
      ≡
      true

    cmsArchivePath :
      String

    cmsArchivePathIsLocalDownload :
      cmsArchivePath
      ≡
      "/home/c/Downloads/HEPData-ins2616304-v1.zip"

    cmsArchiveSHA256 :
      String

    cmsArchiveSHA256IsCanonical :
      cmsArchiveSHA256
      ≡
      "561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"

    cmsArchiveSHA256Verified :
      Bool

    cmsArchiveSHA256VerifiedIsTrue :
      cmsArchiveSHA256Verified ≡ true

    selectedThreadCandidateIsLHCb :
      Contract.selectedThreadCandidate
        Contract.canonicalPenguinDatasetSourceDiscriminator
      ≡
      Contract.lhcbBsMuMuCERN5r7hzC7e34

    readinessSelectedThreadChecksumAuthorityPresent :
      Bool

    readinessSelectedThreadChecksumAuthorityPresentIsFalse :
      readinessSelectedThreadChecksumAuthorityPresent ≡ false

    readinessSelectedThreadChecksumMatchesProjectionArtifact :
      readinessSelectedThreadChecksumAuthorityPresent
      ≡
      selectedThreadChecksumAuthorityPresent readinessProjectionArtifact

    readinessFreezeGateOpen :
      Bool

    readinessFreezeGateOpenIsFalse :
      readinessFreezeGateOpen ≡ false

    readinessAcceptedResidualCandidateClaimedHere :
      Bool

    readinessAcceptedResidualCandidateClaimedHereIsFalse :
      readinessAcceptedResidualCandidateClaimedHere ≡ false

    readinessReducedRemainingBlockers :
      List PenguinCMSChecksumReadinessBlocker

    readinessReducedRemainingBlockersAreCanonical :
      readinessReducedRemainingBlockers
      ≡
      canonicalPenguinCMSChecksumReadinessBlockers

    cmsReadinessSummary :
      List String

open PenguinCMSChecksumPopulatedReadinessReceipt public

canonicalPenguinCMSChecksumPopulatedReadinessReceipt :
  PenguinCMSChecksumPopulatedReadinessReceipt
canonicalPenguinCMSChecksumPopulatedReadinessReceipt =
  record
    { readinessProjectionArtifact =
        canonicalPenguinDecayProjectionArtifactRequest
    ; cmsDatasetChecksumAuthority =
        canonicalCMSResultsDatasetChecksumAuthority
    ; cmsDatasetChecksumAuthorityIsCanonical =
        refl
    ; cmsDatasetSourceCandidateIsCMS =
        refl
    ; cmsDatasetDigestAlgorithmIsSHA256 =
        refl
    ; cmsDatasetPayloadSHA256IsCanonical =
        refl
    ; cmsDatasetPayloadSHA256Verified =
        refl
    ; cmsDatasetAuthorityPresent =
        true
    ; cmsDatasetAuthorityPresentIsTrue =
        refl
    ; cmsTableArtifact =
        Contract.canonicalCMSTableArtifactChecksumCandidate
    ; cmsTableArtifactIsCanonical =
        refl
    ; cmsTableRecordIsCanonical =
        refl
    ; cmsTableDOIIsCanonical =
        refl
    ; cmsTableIdentifierIsCanonical =
        refl
    ; cmsTableSHA256IsCanonical =
        refl
    ; cmsTableSHA256Verified =
        refl
    ; cmsArchivePath =
        "/home/c/Downloads/HEPData-ins2616304-v1.zip"
    ; cmsArchivePathIsLocalDownload =
        refl
    ; cmsArchiveSHA256 =
        "561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"
    ; cmsArchiveSHA256IsCanonical =
        refl
    ; cmsArchiveSHA256Verified =
        true
    ; cmsArchiveSHA256VerifiedIsTrue =
        refl
    ; selectedThreadCandidateIsLHCb =
        refl
    ; readinessSelectedThreadChecksumAuthorityPresent =
        false
    ; readinessSelectedThreadChecksumAuthorityPresentIsFalse =
        refl
    ; readinessSelectedThreadChecksumMatchesProjectionArtifact =
        refl
    ; readinessFreezeGateOpen =
        false
    ; readinessFreezeGateOpenIsFalse =
        refl
    ; readinessAcceptedResidualCandidateClaimedHere =
        false
    ; readinessAcceptedResidualCandidateClaimedHereIsFalse =
        refl
    ; readinessReducedRemainingBlockers =
        canonicalPenguinCMSChecksumReadinessBlockers
    ; readinessReducedRemainingBlockersAreCanonical =
        refl
    ; cmsReadinessSummary =
        "CMS checksum readiness is concrete: HEPData ins2616304 v1 Results table DOI 10.17182/hepdata.135675.v1/t1 table id 1435213 has sha256 08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"
        ∷ "CMS archive /home/c/Downloads/HEPData-ins2616304-v1.zip is verified with sha256 561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"
        ∷ "This receipt is separate from the selected LHCb thread lane; selectedThreadChecksumAuthorityPresent remains false"
        ∷ "Reduced remaining blockers after the CMS checksum are flavio package digest, runtime environment digest, Wilson authority digest, no-posterior-tuning attestation, projection-code freeze hash, and the LHCb artifact checksum if the lane stays thread-selected"
        ∷ "No acceptedResidualCandidate is claimed by this readiness receipt"
        ∷ []
    }

canonicalPenguinCMSReadinessDatasetChecksumPresent :
  cmsDatasetAuthorityPresent
    canonicalPenguinCMSChecksumPopulatedReadinessReceipt
  ≡
  true
canonicalPenguinCMSReadinessDatasetChecksumPresent =
  refl

canonicalPenguinCMSReadinessSelectedThreadChecksumAbsent :
  readinessSelectedThreadChecksumAuthorityPresent
    canonicalPenguinCMSChecksumPopulatedReadinessReceipt
  ≡
  false
canonicalPenguinCMSReadinessSelectedThreadChecksumAbsent =
  refl

canonicalPenguinCMSReadinessReducedBlockers :
  readinessReducedRemainingBlockers
    canonicalPenguinCMSChecksumPopulatedReadinessReceipt
  ≡
  canonicalPenguinCMSChecksumReadinessBlockers
canonicalPenguinCMSReadinessReducedBlockers =
  refl
