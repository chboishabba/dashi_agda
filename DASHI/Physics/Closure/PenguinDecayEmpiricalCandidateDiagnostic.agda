module DASHI.Physics.Closure.PenguinDecayEmpiricalCandidateDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Defect
import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority as Baseline
import DASHI.Physics.Closure.PenguinDecayProjectionArtifact as Artifact
import DASHI.Physics.Closure.PenguinDecayResidualComparisonLaw as Law
import DASHI.Physics.Closure.PenguinDecayLHCbChecksumAcceptedResidualReceipt as LHCb
import DASHI.Physics.Closure.ResidualComparisonLaw as Residual

------------------------------------------------------------------------
-- Penguin-decay empirical candidate diagnostic.
--
-- This is the integrated empirical-contact receipt for the thread-selected
-- penguin lane:
--
--   ProjectionDefectReceipt
--     -> ObservableContract
--     -> SMBaselineAuthority
--     -> ProjectionArtifact
--     -> ResidualComparisonLaw
--     -> EmpiricalCandidateDiagnostic
--
-- Empirical contact here means the typed diagnostic surfaces are inhabited
-- and wired together.  It does not mean accepted authority, an executed
-- projection, an empirical residual result, a Standard-Model tension claim, or
-- non-Standard-Model promotion.

data PenguinEmpiricalCandidateState : Set where
  empiricalContactReachedPromotionBlocked :
    PenguinEmpiricalCandidateState

data PenguinEmpiricalPromotionToken : Set where

penguinEmpiricalPromotionImpossibleHere :
  PenguinEmpiricalPromotionToken →
  ⊥
penguinEmpiricalPromotionImpossibleHere ()

data PenguinEmpiricalCandidateBoundary : Set where
  contactMeansDiagnosticSurfacesNotDiscovery :
    PenguinEmpiricalCandidateBoundary
  observableContractInhabitedButAuthorityStillRequired :
    PenguinEmpiricalCandidateBoundary
  smBaselineAuthorityRequestedButNotAccepted :
    PenguinEmpiricalCandidateBoundary
  projectionArtifactEnvelopePresentButNoRunResult :
    PenguinEmpiricalCandidateBoundary
  residualComparisonLawRequestedButInsufficientAuthority :
    PenguinEmpiricalCandidateBoundary
  expectedResidualCandidateShapeAuthorityGated :
    PenguinEmpiricalCandidateBoundary
  noNonSMDiscoveryClaim :
    PenguinEmpiricalCandidateBoundary
  noEmpiricalPromotionConstructed :
    PenguinEmpiricalCandidateBoundary

canonicalPenguinEmpiricalCandidateBoundary :
  List PenguinEmpiricalCandidateBoundary
canonicalPenguinEmpiricalCandidateBoundary =
  contactMeansDiagnosticSurfacesNotDiscovery
  ∷ observableContractInhabitedButAuthorityStillRequired
  ∷ smBaselineAuthorityRequestedButNotAccepted
  ∷ projectionArtifactEnvelopePresentButNoRunResult
  ∷ residualComparisonLawRequestedButInsufficientAuthority
  ∷ expectedResidualCandidateShapeAuthorityGated
  ∷ noNonSMDiscoveryClaim
  ∷ noEmpiricalPromotionConstructed
  ∷ []

data PenguinEmpiricalMissingAuthorityBlocker : Set where
  missingFlavioVersionDigestAuthority :
    PenguinEmpiricalMissingAuthorityBlocker
  missingC9C10WilsonAuthorityDigest :
    PenguinEmpiricalMissingAuthorityBlocker
  missingHEPDataTableChecksumAuthority :
    PenguinEmpiricalMissingAuthorityBlocker
  missingCKMSourceCommitAuthority :
    PenguinEmpiricalMissingAuthorityBlocker
  missingFreezeTupleAuthorityPopulation :
    PenguinEmpiricalMissingAuthorityBlocker
  missingNoPosteriorTuningAttestationAuthority :
    PenguinEmpiricalMissingAuthorityBlocker

canonicalPenguinEmpiricalMissingAuthorityBlockers :
  List PenguinEmpiricalMissingAuthorityBlocker
canonicalPenguinEmpiricalMissingAuthorityBlockers =
  missingFlavioVersionDigestAuthority
  ∷ missingC9C10WilsonAuthorityDigest
  ∷ missingHEPDataTableChecksumAuthority
  ∷ missingCKMSourceCommitAuthority
  ∷ missingFreezeTupleAuthorityPopulation
  ∷ missingNoPosteriorTuningAttestationAuthority
  ∷ []

record PenguinDecayEmpiricalCandidateDiagnostic : Setω where
  field
    currentState :
      PenguinEmpiricalCandidateState

    projectionDefectReceipt :
      Defect.PenguinDecayProjectionDefectReceipt

    projectionDefectReceiptIsCanonical :
      projectionDefectReceipt
      ≡
      Defect.canonicalPenguinDecayProjectionDefectReceipt

    observableContract :
      Contract.PenguinDecayObservableContract

    observableContractIsCanonical :
      observableContract
      ≡
      Contract.canonicalPenguinDecayObservableContract

    selectedObservableDecayIsBToSLeptonPair :
      Contract.PenguinDecayObservableContract.selectedDecay
        observableContract
      ≡
      Defect.bToSLeptonPair

    smBaselineAuthority :
      Baseline.SMBaselineAuthorityRequestDiagnostic

    smBaselineAuthorityIsCanonical :
      smBaselineAuthority
      ≡
      Baseline.canonicalSMBaselineAuthorityRequestDiagnostic

    smBaselineStillBlocked :
      Baseline.SMBaselineAuthorityRequestDiagnostic.status
        smBaselineAuthority
      ≡
      Baseline.blockedAwaitingAcceptedSMBaselineAuthority

    projectionArtifact :
      Artifact.PenguinDecayProjectionArtifactRequest

    projectionArtifactHasNoEmpiricalResult :
      Artifact.PenguinDecayProjectionArtifactRequest.empiricalResultConstructedHere
        projectionArtifact
      ≡
      false

    datasetSourceDiscriminator :
      Contract.PenguinDatasetSourceDiscriminator

    datasetSourceDiscriminatorIsCanonical :
      datasetSourceDiscriminator
      ≡
      Contract.canonicalPenguinDatasetSourceDiscriminator

    cmsChecksumAuthorityCandidate :
      Artifact.SuppliedPenguinDatasetChecksumAuthority

    cmsChecksumAuthorityCandidateIsCanonical :
      cmsChecksumAuthorityCandidate
      ≡
      Artifact.canonicalCMSResultsDatasetChecksumAuthority

    selectedThreadChecksumAuthorityPresent :
      Bool

    selectedThreadChecksumAuthorityPresentIsFalse :
      selectedThreadChecksumAuthorityPresent ≡ false

    cmsChecksumReadinessReceipt :
      Artifact.PenguinCMSChecksumPopulatedReadinessReceipt

    cmsReadinessDatasetChecksumAuthorityPresent :
      Artifact.cmsDatasetAuthorityPresent cmsChecksumReadinessReceipt
      ≡
      true

    cmsReadinessSelectedThreadChecksumAuthorityPresentIsFalse :
      Artifact.readinessSelectedThreadChecksumAuthorityPresent
        cmsChecksumReadinessReceipt
      ≡
      false

    cmsReadinessReducedRemainingBlockers :
      List Artifact.PenguinCMSChecksumReadinessBlocker

    cmsReadinessReducedRemainingBlockersAreCanonical :
      cmsReadinessReducedRemainingBlockers
      ≡
      Artifact.canonicalPenguinCMSChecksumReadinessBlockers

    cmsReadinessAcceptedResidualCandidateClaimedHereIsFalse :
      Artifact.readinessAcceptedResidualCandidateClaimedHere
        cmsChecksumReadinessReceipt
      ≡
      false

    residualComparisonLaw :
      Law.PenguinDecayResidualComparisonLaw

    residualComparisonLawIsCanonical :
      residualComparisonLaw
      ≡
      Law.canonicalPenguinDecayResidualComparisonLaw

    lhcbChecksumAcceptedResidualReceipt :
      LHCb.LHCbChecksumAcceptedResidualSurfaceReceipt

    lhcbSelectedThreadChecksumBound :
      LHCb.selectedThreadSupplementaryChecksumPresent
        lhcbChecksumAcceptedResidualReceipt
      ≡
      true

    lhcbSupplementaryChecksumIsSelectedThread :
      LHCb.sourceCandidate
        (LHCb.lhcbSupplementaryChecksumBinding
          lhcbChecksumAcceptedResidualReceipt)
      ≡
      Contract.lhcbPRD105012010CDS2779103

    lhcbHEPDataValueTableChecksumBound :
      LHCb.hepdataValueTableChecksumReceiptPresent
        lhcbChecksumAcceptedResidualReceipt
      ≡
      true

    lhcbHEPDataCovarianceTableChecksumBound :
      LHCb.hepdataCovarianceTableChecksumReceiptPresent
        lhcbChecksumAcceptedResidualReceipt
      ≡
      true

    lhcbResidualVectorReceiptBound :
      LHCb.p5PrimeResidualVectorComparison
        lhcbChecksumAcceptedResidualReceipt
      ≡
      Law.canonicalP5PrimeResidualVectorComparison

    lhcbResidualVectorStatusIsBorderline :
      LHCb.p5PrimeResidualVectorStatus
        lhcbChecksumAcceptedResidualReceipt
      ≡
      Law.p5PrimeBorderlineAnomalyCandidate

    lhcbAcceptedResidualCandidateConstructedHereIsFalse :
      LHCb.acceptedResidualCandidateConstructedHere
        lhcbChecksumAcceptedResidualReceipt
      ≡
      false

    lhcbP5PrimeAcceptedResidualCandidateConstructedHereIsFalse :
      LHCb.p5PrimeResidualVectorAcceptedCandidateConstructedHere
        lhcbChecksumAcceptedResidualReceipt
      ≡
      false

    empiricalContactReached :
      Bool

    empiricalContactReachedIsTrue :
      empiricalContactReached ≡ true

    residualComparisonOutcomeIsInsufficientAuthority :
      Law.PenguinDecayResidualComparisonLaw.currentOutcome
        residualComparisonLaw
      ≡
      Law.insufficientAuthority

    p5PrimeResidualVectorComparison :
      Law.P5PrimeResidualVectorComparison

    p5PrimeResidualVectorComparisonIsLawCanonical :
      p5PrimeResidualVectorComparison
      ≡
      Law.PenguinDecayResidualComparisonLaw.p5PrimeResidualVectorComparison
        residualComparisonLaw

    anomalyCandidateClassified :
      Law.P5PrimeResidualVectorStatus

    anomalyCandidateClassifiedIsP5PrimeBorderline :
      anomalyCandidateClassified
      ≡
      Law.p5PrimeBorderlineAnomalyCandidate

    anomalyCandidateClassifiedAgreesWithP5PrimeTable :
      anomalyCandidateClassified
      ≡
      Law.P5PrimeResidualVectorComparison.vectorStatus
        p5PrimeResidualVectorComparison

    expectedResidualComparison :
      Law.PenguinExpectedResidualComparison

    expectedResidualComparisonIsLawCanonical :
      expectedResidualComparison
      ≡
      Law.PenguinDecayResidualComparisonLaw.expectedResidualComparison
        residualComparisonLaw

    expectedResidualComparisonIsArtifactBoundAtMostTwoSigma :
      expectedResidualComparison
      ≡
      Law.artifactBoundAtMostTwoSigmaPenguinResidualComparison

    acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent :
      (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
      Residual.classifyResidualCandidate
        (Law.acceptedAuthorityState prerequisites)
        (Law.freezeState prerequisites)
        (Law.dataState prerequisites)
        (Law.theoryUncertaintyState prerequisites)
        Residual.sigmaAtMostTwo
      ≡
      Law.acceptedResidualCandidate

    acceptedResidualCandidateBridgeUsesFrozenTuple :
      (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.tupleFields (Law.freezeTuple prerequisites)
      ≡
      Artifact.canonicalPenguinPreRegistrationTupleFields

    acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers :
      (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
      Law.noPosteriorTuningBlockers prerequisites
      ≡
      Artifact.canonicalPenguinNoPosteriorTuningBlockers

    acceptedResidualCandidateBridgeUsesSuppliedChecksum :
      (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.digestAlgorithm (Law.datasetChecksumAuthority prerequisites)
      ≡
      "sha256"

    artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority :
      (freeze : Residual.ResidualFreezeState) →
      (dataState : Residual.ResidualDataState) →
      (theory : Residual.ResidualTheoryUncertaintyState) →
      Residual.classifyResidualCandidate
        Residual.authorityMissing
        freeze
        dataState
        theory
        Residual.sigmaAtMostTwo
      ≡
      Law.insufficientAuthority

    missingAuthorityBlockers :
      List PenguinEmpiricalMissingAuthorityBlocker

    missingAuthorityBlockersAreCanonical :
      missingAuthorityBlockers
      ≡
      canonicalPenguinEmpiricalMissingAuthorityBlockers

    projectionDefectSurfaceInhabited :
      Bool

    projectionDefectSurfaceInhabitedIsTrue :
      projectionDefectSurfaceInhabited ≡ true

    observableContractSurfaceInhabited :
      Bool

    observableContractSurfaceInhabitedIsTrue :
      observableContractSurfaceInhabited ≡ true

    smBaselineAuthoritySurfaceInhabited :
      Bool

    smBaselineAuthoritySurfaceInhabitedIsTrue :
      smBaselineAuthoritySurfaceInhabited ≡ true

    projectionArtifactSurfaceInhabited :
      Bool

    projectionArtifactSurfaceInhabitedIsTrue :
      projectionArtifactSurfaceInhabited ≡ true

    residualComparisonLawSurfaceInhabited :
      Bool

    residualComparisonLawSurfaceInhabitedIsTrue :
      residualComparisonLawSurfaceInhabited ≡ true

    empiricalPromotion :
      Bool

    empiricalPromotionIsFalse :
      empiricalPromotion ≡ false

    nonSMDiscoveryClaim :
      Bool

    nonSMDiscoveryClaimIsFalse :
      nonSMDiscoveryClaim ≡ false

    promotionTokenBlocked :
      PenguinEmpiricalPromotionToken →
      ⊥

    nonPromotionBoundary :
      List PenguinEmpiricalCandidateBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ canonicalPenguinEmpiricalCandidateBoundary

    roadmapSummary :
      List String

open PenguinDecayEmpiricalCandidateDiagnostic public

canonicalPenguinDecayEmpiricalCandidateDiagnostic :
  PenguinDecayEmpiricalCandidateDiagnostic
canonicalPenguinDecayEmpiricalCandidateDiagnostic =
  record
    { currentState =
        empiricalContactReachedPromotionBlocked
    ; projectionDefectReceipt =
        Defect.canonicalPenguinDecayProjectionDefectReceipt
    ; projectionDefectReceiptIsCanonical =
        refl
    ; observableContract =
        Contract.canonicalPenguinDecayObservableContract
    ; observableContractIsCanonical =
        refl
    ; selectedObservableDecayIsBToSLeptonPair =
        refl
    ; smBaselineAuthority =
        Baseline.canonicalSMBaselineAuthorityRequestDiagnostic
    ; smBaselineAuthorityIsCanonical =
        refl
    ; smBaselineStillBlocked =
        refl
    ; projectionArtifact =
        Artifact.canonicalPenguinDecayProjectionArtifactRequest
    ; projectionArtifactHasNoEmpiricalResult =
        refl
    ; datasetSourceDiscriminator =
        Contract.canonicalPenguinDatasetSourceDiscriminator
    ; datasetSourceDiscriminatorIsCanonical =
        refl
    ; cmsChecksumAuthorityCandidate =
        Artifact.canonicalCMSResultsDatasetChecksumAuthority
    ; cmsChecksumAuthorityCandidateIsCanonical =
        refl
    ; selectedThreadChecksumAuthorityPresent =
        false
    ; selectedThreadChecksumAuthorityPresentIsFalse =
        refl
    ; cmsChecksumReadinessReceipt =
        Artifact.canonicalPenguinCMSChecksumPopulatedReadinessReceipt
    ; cmsReadinessDatasetChecksumAuthorityPresent =
        refl
    ; cmsReadinessSelectedThreadChecksumAuthorityPresentIsFalse =
        refl
    ; cmsReadinessReducedRemainingBlockers =
        Artifact.canonicalPenguinCMSChecksumReadinessBlockers
    ; cmsReadinessReducedRemainingBlockersAreCanonical =
        refl
    ; cmsReadinessAcceptedResidualCandidateClaimedHereIsFalse =
        refl
    ; residualComparisonLaw =
        Law.canonicalPenguinDecayResidualComparisonLaw
    ; residualComparisonLawIsCanonical =
        refl
    ; lhcbChecksumAcceptedResidualReceipt =
        LHCb.canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
    ; lhcbSelectedThreadChecksumBound =
        refl
    ; lhcbSupplementaryChecksumIsSelectedThread =
        refl
    ; lhcbHEPDataValueTableChecksumBound =
        refl
    ; lhcbHEPDataCovarianceTableChecksumBound =
        refl
    ; lhcbResidualVectorReceiptBound =
        refl
    ; lhcbResidualVectorStatusIsBorderline =
        refl
    ; lhcbAcceptedResidualCandidateConstructedHereIsFalse =
        refl
    ; lhcbP5PrimeAcceptedResidualCandidateConstructedHereIsFalse =
        refl
    ; empiricalContactReached =
        true
    ; empiricalContactReachedIsTrue =
        refl
    ; residualComparisonOutcomeIsInsufficientAuthority =
        refl
    ; p5PrimeResidualVectorComparison =
        Law.PenguinDecayResidualComparisonLaw.p5PrimeResidualVectorComparison
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; p5PrimeResidualVectorComparisonIsLawCanonical =
        refl
    ; anomalyCandidateClassified =
        Law.p5PrimeBorderlineAnomalyCandidate
    ; anomalyCandidateClassifiedIsP5PrimeBorderline =
        refl
    ; anomalyCandidateClassifiedAgreesWithP5PrimeTable =
        refl
    ; expectedResidualComparison =
        Law.artifactBoundAtMostTwoSigmaPenguinResidualComparison
    ; expectedResidualComparisonIsLawCanonical =
        refl
    ; expectedResidualComparisonIsArtifactBoundAtMostTwoSigma =
        refl
    ; acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent =
        Law.acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; acceptedResidualCandidateBridgeUsesFrozenTuple =
        Law.acceptedResidualCandidateBridgeUsesFrozenTuple
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers =
        Law.acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; acceptedResidualCandidateBridgeUsesSuppliedChecksum =
        Law.acceptedResidualCandidateBridgeUsesSuppliedChecksum
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority =
        Law.artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; missingAuthorityBlockers =
        canonicalPenguinEmpiricalMissingAuthorityBlockers
    ; missingAuthorityBlockersAreCanonical =
        refl
    ; projectionDefectSurfaceInhabited =
        true
    ; projectionDefectSurfaceInhabitedIsTrue =
        refl
    ; observableContractSurfaceInhabited =
        true
    ; observableContractSurfaceInhabitedIsTrue =
        refl
    ; smBaselineAuthoritySurfaceInhabited =
        true
    ; smBaselineAuthoritySurfaceInhabitedIsTrue =
        refl
    ; projectionArtifactSurfaceInhabited =
        true
    ; projectionArtifactSurfaceInhabitedIsTrue =
        refl
    ; residualComparisonLawSurfaceInhabited =
        true
    ; residualComparisonLawSurfaceInhabitedIsTrue =
        refl
    ; empiricalPromotion =
        false
    ; empiricalPromotionIsFalse =
        refl
    ; nonSMDiscoveryClaim =
        false
    ; nonSMDiscoveryClaimIsFalse =
        refl
    ; promotionTokenBlocked =
        penguinEmpiricalPromotionImpossibleHere
    ; nonPromotionBoundary =
        canonicalPenguinEmpiricalCandidateBoundary
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; roadmapSummary =
        "empirical contact reached: projection-defect receipt, observable contract, SM baseline authority request, projection artifact envelope, and residual comparison law request are all inhabited"
        ∷ "canonical selected decay is b -> s lepton pair and the residual comparison outcome remains insufficientAuthority"
        ∷ "empiricalContactReached is true only after binding the LHCb checksum/accepted-residual surface receipt"
        ∷ "the bound P5' residual-vector receipt classifies the anomaly candidate as p5PrimeBorderlineAnomalyCandidate"
        ∷ "the selected-thread supplementary checksum and the current LHCb P5' HEPData value/correlation-table checksums are bound"
        ∷ "artifact-bound sub-2-sigma residual comparisons have an acceptedResidualCandidate theorem only after a selected-thread sha256 dataset checksum authority plus authority, freeze, data, and theory-control prerequisites are present"
        ∷ "canonical diagnostic records CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results with sha256 08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb, but the thread-selected LHCb DOI 10.1103/PhysRevD.105.012010 / CDS 2779103 checksum is missing"
        ∷ "CMS checksum authority is populated as a candidate only; selectedThreadChecksumAuthorityPresent is false, so no LHCb-specific promotion occurs"
        ∷ "CMS-readiness reduced blockers are flavio package digest, runtime environment digest, Wilson authority digest, no-posterior-tuning attestation, projection-code freeze hash, and the LHCb artifact checksum if this remains the selected thread lane"
        ∷ "canonical diagnostic remains fail-closed and does not claim acceptedResidualCandidate because accepted authority, complete freeze, selected-thread data, and controlled-theory prerequisites are not all present"
        ∷ "empirical contact does not mean discovery, accepted external authority, executed projection result, or empirical adequacy promotion"
        ∷ []
    }

canonicalPenguinEmpiricalContactState :
  currentState canonicalPenguinDecayEmpiricalCandidateDiagnostic
  ≡
  empiricalContactReachedPromotionBlocked
canonicalPenguinEmpiricalContactState =
  refl

canonicalPenguinEmpiricalContactReached :
  empiricalContactReached canonicalPenguinDecayEmpiricalCandidateDiagnostic
  ≡
  true
canonicalPenguinEmpiricalContactReached =
  refl

canonicalPenguinEmpiricalAnomalyCandidateClassified :
  anomalyCandidateClassified canonicalPenguinDecayEmpiricalCandidateDiagnostic
  ≡
  Law.p5PrimeBorderlineAnomalyCandidate
canonicalPenguinEmpiricalAnomalyCandidateClassified =
  refl

canonicalPenguinEmpiricalPromotionStillBlocked :
  empiricalPromotion canonicalPenguinDecayEmpiricalCandidateDiagnostic
  ≡
  false
canonicalPenguinEmpiricalPromotionStillBlocked =
  refl

canonicalPenguinEmpiricalExpectedResidualAcceptedWhenPrerequisitesPresent :
  (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
  Residual.classifyResidualCandidate
    (Law.acceptedAuthorityState prerequisites)
    (Law.freezeState prerequisites)
    (Law.dataState prerequisites)
    (Law.theoryUncertaintyState prerequisites)
    Residual.sigmaAtMostTwo
  ≡
  Law.acceptedResidualCandidate
canonicalPenguinEmpiricalExpectedResidualAcceptedWhenPrerequisitesPresent =
  acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent
    canonicalPenguinDecayEmpiricalCandidateDiagnostic

canonicalPenguinEmpiricalExpectedResidualStillInsufficientWithoutAuthority :
  (freeze : Residual.ResidualFreezeState) →
  (dataState : Residual.ResidualDataState) →
  (theory : Residual.ResidualTheoryUncertaintyState) →
  Residual.classifyResidualCandidate
    Residual.authorityMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo
  ≡
  Law.insufficientAuthority
canonicalPenguinEmpiricalExpectedResidualStillInsufficientWithoutAuthority =
  artifactBoundAtMostTwoSigmaStillInsufficientWithoutAuthority
    canonicalPenguinDecayEmpiricalCandidateDiagnostic

canonicalPenguinEmpiricalCMSChecksumAuthorityPresent :
  Artifact.cmsDatasetAuthorityPresent
    (cmsChecksumReadinessReceipt
      canonicalPenguinDecayEmpiricalCandidateDiagnostic)
  ≡
  true
canonicalPenguinEmpiricalCMSChecksumAuthorityPresent =
  refl

canonicalPenguinEmpiricalSelectedThreadChecksumStillAbsent :
  Artifact.readinessSelectedThreadChecksumAuthorityPresent
    (cmsChecksumReadinessReceipt
      canonicalPenguinDecayEmpiricalCandidateDiagnostic)
  ≡
  false
canonicalPenguinEmpiricalSelectedThreadChecksumStillAbsent =
  refl

canonicalPenguinEmpiricalCMSReducedReadinessBlockers :
  cmsReadinessReducedRemainingBlockers
    canonicalPenguinDecayEmpiricalCandidateDiagnostic
  ≡
  Artifact.canonicalPenguinCMSChecksumReadinessBlockers
canonicalPenguinEmpiricalCMSReducedReadinessBlockers =
  refl
