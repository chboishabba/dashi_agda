module DASHI.Physics.Closure.PenguinDecayLHCbChecksumAcceptedResidualReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayResidualComparisonLaw as Law
import DASHI.Physics.Closure.ResidualComparisonLaw as Residual

------------------------------------------------------------------------
-- Chain C1: LHCb checksum and accepted-residual surface.
--
-- The selected thread lane names LHCb-PAPER-2021-008 / CDS 2779103.  This
-- module records the concrete checksum that was obtainable for the CDS
-- supplementary archive and keeps the residual surface fail-closed: the CDS
-- archive is not a HEPData value/covariance table receipt and is not a
-- residual-vector artifact.  The separate ins1486676 route is now bound as
-- the HEPData Table 3 normalised-moment covariance artifact; it remains
-- distinct from the P5' B0 -> K*0 mu+ mu- angular-analysis lane.  The
-- reachable P5' machine-readable value-table route is the current full
-- Run 1+2 LHCb HEPData record 10.17182/hepdata.167733.v1/t2; the claimed
-- 10.17182/hepdata.89409 route did not resolve here.  For the requested
-- LHCb-PAPER-2020-002 / arXiv:2003.04831 artifact, the value table is bound
-- from LHCb/CDS/arXiv TeX rather than HEPData.

data LHCbChecksumArtifactStatus : Set where
  runOneRunTwoFullDatasetPublicResultRecorded :
    LHCbChecksumArtifactStatus

  claimedHEPData160745RouteMismatchesP5PrimeLane :
    LHCbChecksumArtifactStatus

  suppliedIns2922449Table16LocalYAMLRejected :
    LHCbChecksumArtifactStatus

  fallbackIns1798504RouteRecorded :
    LHCbChecksumArtifactStatus

  cdsSupplementaryArchiveChecksumBound :
    LHCbChecksumArtifactStatus

  cernRepositoryThesisRouteEvidenceRecorded :
    LHCbChecksumArtifactStatus

  hepdataIns2101841RouteIsUnrelatedInspireRecord :
    LHCbChecksumArtifactStatus

  selectedLHCbInspire1908217HasNoHEPDataTableHere :
    LHCbChecksumArtifactStatus

  missingHEPDataValueAndCovarianceTableReceipt :
    LHCbChecksumArtifactStatus

  hepdataIns1486676RecordMetadataFound :
    LHCbChecksumArtifactStatus

  hepdataIns1486676Table3NormalisedMomentCovarianceBound :
    LHCbChecksumArtifactStatus

  hepdataIns1486676IsNotP5PrimeAngularAnalysis :
    LHCbChecksumArtifactStatus

  hepdataIns1486676P5PrimeValueCovarianceTableFileMissing :
    LHCbChecksumArtifactStatus

  hepdataRun12P5PrimeValueTableBound :
    LHCbChecksumArtifactStatus

  hepdata89409RouteDidNotResolve :
    LHCbChecksumArtifactStatus

  lhcb2020P5PrimeValueTableBound :
    LHCbChecksumArtifactStatus

  hepdata2020P5PrimeRouteAbsent :
    LHCbChecksumArtifactStatus

  missingResidualVectorArtifact :
    LHCbChecksumArtifactStatus

data LHCbAcceptedResidualSurfaceStatus : Set where
  acceptedResidualTheoremAvailableOnlyUnderPrerequisites :
    LHCbAcceptedResidualSurfaceStatus

  acceptedResidualCandidateNotConstructedHere :
    LHCbAcceptedResidualSurfaceStatus

canonicalLHCbChecksumArtifactStatuses :
  List LHCbChecksumArtifactStatus
canonicalLHCbChecksumArtifactStatuses =
  runOneRunTwoFullDatasetPublicResultRecorded
  ∷ claimedHEPData160745RouteMismatchesP5PrimeLane
  ∷ suppliedIns2922449Table16LocalYAMLRejected
  ∷ fallbackIns1798504RouteRecorded
  ∷ cdsSupplementaryArchiveChecksumBound
  ∷ cernRepositoryThesisRouteEvidenceRecorded
  ∷ hepdataIns2101841RouteIsUnrelatedInspireRecord
  ∷ selectedLHCbInspire1908217HasNoHEPDataTableHere
  ∷ missingHEPDataValueAndCovarianceTableReceipt
  ∷ hepdataIns1486676RecordMetadataFound
  ∷ hepdataIns1486676Table3NormalisedMomentCovarianceBound
  ∷ hepdataIns1486676IsNotP5PrimeAngularAnalysis
  ∷ hepdataIns1486676P5PrimeValueCovarianceTableFileMissing
  ∷ hepdataRun12P5PrimeValueTableBound
  ∷ hepdata89409RouteDidNotResolve
  ∷ lhcb2020P5PrimeValueTableBound
  ∷ hepdata2020P5PrimeRouteAbsent
  ∷ missingResidualVectorArtifact
  ∷ []

canonicalLHCbAcceptedResidualSurfaceStatuses :
  List LHCbAcceptedResidualSurfaceStatus
canonicalLHCbAcceptedResidualSurfaceStatuses =
  acceptedResidualTheoremAvailableOnlyUnderPrerequisites
  ∷ acceptedResidualCandidateNotConstructedHere
  ∷ []

record LHCbCDSSupplementaryChecksumBinding : Set where
  constructor mkLHCbCDSSupplementaryChecksumBinding
  field
    sourceCandidate :
      Contract.PenguinDatasetSourceCandidateName

    sourceCandidateIsLHCb :
      sourceCandidate
      ≡
      Contract.lhcbPRD105012010CDS2779103

    digestAlgorithm :
      String

    digestAlgorithmIsSHA256 :
      digestAlgorithm
      ≡
      "sha256"

    payloadSHA256 :
      String

    payloadSHA256IsDownloadedSupplementaryZip :
      payloadSHA256
      ≡
      "68bf6ab48ca104c2e37f1edeb64fbde59d4542600adf78c28869f092daef7fb8"

    artifactURL :
      String

    artifactURLIsCDSVersionedSupplementaryZip :
      artifactURL
      ≡
      "https://cds.cern.ch/record/2779103/files/LHCb-PAPER-2021-008-supplementary.zip?version=1"

    artifactIsValueTableReceipt :
      Bool

    artifactIsValueTableReceiptIsFalse :
      artifactIsValueTableReceipt
      ≡
      false

    artifactIsCovarianceTableReceipt :
      Bool

    artifactIsCovarianceTableReceiptIsFalse :
      artifactIsCovarianceTableReceipt
      ≡
      false

    artifactIsResidualVector :
      Bool

    artifactIsResidualVectorIsFalse :
      artifactIsResidualVector
      ≡
      false

open LHCbCDSSupplementaryChecksumBinding public

canonicalLHCbCDSSupplementaryChecksumBinding :
  LHCbCDSSupplementaryChecksumBinding
canonicalLHCbCDSSupplementaryChecksumBinding =
  mkLHCbCDSSupplementaryChecksumBinding
    Contract.lhcbPRD105012010CDS2779103
    refl
    "sha256"
    refl
    "68bf6ab48ca104c2e37f1edeb64fbde59d4542600adf78c28869f092daef7fb8"
    refl
    "https://cds.cern.ch/record/2779103/files/LHCb-PAPER-2021-008-supplementary.zip?version=1"
    refl
    false
    refl
    false
    refl
    false
    refl

record LHCbP5PrimeRun12PublicResultBinding : Set where
  constructor mkLHCbP5PrimeRun12PublicResultBinding
  field
    publicResultURL :
      String

    publicResultURLIsCanonical :
      publicResultURL
      ≡
      "https://cds.cern.ch/record/2951844?ln=en"

    publicResultDate :
      String

    publicResultDateIsSeptember2025 :
      publicResultDate
      ≡
      "2025-12-16"

    publicResultPaperIdentifier :
      String

    publicResultPaperIdentifierIsCanonical :
      publicResultPaperIdentifier
      ≡
      "LHCb-PAPER-2025-041 / arXiv:2512.18053 / CDS:2951844"

    publicResultDataset :
      String

    publicResultDatasetIsFullRunOneRunTwo :
      publicResultDataset
      ≡
      "8.4 fb^-1 from 2011, 2012, and 2016-2018 LHCb data"

    publicResultObservable :
      String

    publicResultObservableIsP5PrimeAndAFB :
      publicResultObservable
      ≡
      "B0 -> K*0 mu+ mu- angular observables P5' and A_FB"

    publicResultGlobalTension :
      String

    publicResultGlobalTensionIsFourSigma :
      publicResultGlobalTension
      ≡
      "public LHCb summary reports 4 sigma global-fit tension with SM predictions"

    publicResultIsMachineReadableHEPDataReceipt :
      Bool

    publicResultIsMachineReadableHEPDataReceiptIsFalse :
      publicResultIsMachineReadableHEPDataReceipt
      ≡
      false

open LHCbP5PrimeRun12PublicResultBinding public

canonicalLHCbP5PrimeRun12PublicResultBinding :
  LHCbP5PrimeRun12PublicResultBinding
canonicalLHCbP5PrimeRun12PublicResultBinding =
  mkLHCbP5PrimeRun12PublicResultBinding
    "https://cds.cern.ch/record/2951844?ln=en"
    refl
    "2025-12-16"
    refl
    "LHCb-PAPER-2025-041 / arXiv:2512.18053 / CDS:2951844"
    refl
    "8.4 fb^-1 from 2011, 2012, and 2016-2018 LHCb data"
    refl
    "B0 -> K*0 mu+ mu- angular observables P5' and A_FB"
    refl
    "public LHCb summary reports 4 sigma global-fit tension with SM predictions"
    refl
    false
    refl

record HEPDataIns1486676LocalSearchBinding : Set where
  constructor mkHEPDataIns1486676LocalSearchBinding
  field
    localMetadataPath :
      String

    localMetadataPathIsDownloadsRecordJSON :
      localMetadataPath
      ≡
      "/home/c/Downloads/ins1486676.json"

    localMetadataSHA256 :
      String

    localMetadataSHA256IsObserved :
      localMetadataSHA256
      ≡
      "fc6f50bc02c70395fb1389888d47c873a8db56d0752cd340152ddf51844ebc85"

    localMetadataByteCount :
      String

    localMetadataByteCountIsObserved :
      localMetadataByteCount
      ≡
      "7834"

    hepdataRecordIdentifier :
      String

    hepdataRecordIdentifierIsIns1486676 :
      hepdataRecordIdentifier
      ≡
      "ins1486676 / HEPData 75193 v1"

    tableOneDownloadURL :
      String

    tableOneDownloadURLIsMetadataRoute :
      tableOneDownloadURL
      ≡
      "https://www.hepdata.net/download/table/ins1486676/Table 1/json"

    tableTwoDownloadURL :
      String

    tableTwoDownloadURLIsMetadataRoute :
      tableTwoDownloadURL
      ≡
      "https://www.hepdata.net/download/table/ins1486676/Table 2/json"

    tableThreeDownloadURL :
      String

    tableThreeDownloadURLIsMetadataRoute :
      tableThreeDownloadURL
      ≡
      "https://www.hepdata.net/download/table/ins1486676/Table 3/json"

    tableThreeRecordDataURL :
      String

    tableThreeRecordDataURLIsCanonical :
      tableThreeRecordDataURL
      ≡
      "https://www.hepdata.net/record/data/75193/66907/1/0"

    hepdataRecordDOI :
      String

    hepdataRecordDOIIsCanonical :
      hepdataRecordDOI
      ≡
      "10.17182/hepdata.75193.v1"

    hepdataCovarianceTableDOI :
      String

    hepdataCovarianceTableDOIIsTable3 :
      hepdataCovarianceTableDOI
      ≡
      "10.17182/hepdata.75193.v1/t3"

    hepdataCovarianceTableFile :
      String

    hepdataCovarianceTableFileIsLocalRecordDataJSON :
      hepdataCovarianceTableFile
      ≡
      "scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json"

    hepdataCovarianceTableSHA256 :
      String

    hepdataCovarianceTableSHA256IsCanonical :
      hepdataCovarianceTableSHA256
      ≡
      "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"

    hepdataCovarianceTableByteCount :
      String

    hepdataCovarianceTableByteCountIsObserved :
      hepdataCovarianceTableByteCount
      ≡
      "258422"

    hepdataCovarianceTableEntryCount :
      String

    hepdataCovarianceTableEntryCountIsFortyByForty :
      hepdataCovarianceTableEntryCount
      ≡
      "1600"

    hepdataCovarianceTableDescription :
      String

    hepdataCovarianceTableDescriptionIsNormalisedMomentCovariance :
      hepdataCovarianceTableDescription
      ≡
      "Full covariance matrix of the normalised moments. The statistical and systematic uncertainties are combined."

    hepdataCovarianceTableQ2Range :
      String

    hepdataCovarianceTableQ2RangeIsOnePointOneToSix :
      hepdataCovarianceTableQ2Range
      ≡
      "1.1-6.0 GeV^2"

    hepdataCovarianceArtifactBound :
      Bool

    hepdataCovarianceArtifactBoundIsTrue :
      hepdataCovarianceArtifactBound
      ≡
      true

    hepdataCovarianceArtifactIsP5PrimeCovariance :
      Bool

    hepdataCovarianceArtifactIsP5PrimeCovarianceIsFalse :
      hepdataCovarianceArtifactIsP5PrimeCovariance
      ≡
      false

    directDownloadYAMLTransportSucceeded :
      Bool

    directDownloadYAMLTransportSucceededIsFalse :
      directDownloadYAMLTransportSucceeded
      ≡
      false

    metadataContainsP5PrimeTablePayload :
      Bool

    metadataContainsP5PrimeTablePayloadIsFalse :
      metadataContainsP5PrimeTablePayload
      ≡
      false

    metadataContainsQ2FourSixSixEightP5PrimeCovariance :
      Bool

    metadataContainsQ2FourSixSixEightP5PrimeCovarianceIsFalse :
      metadataContainsQ2FourSixSixEightP5PrimeCovariance
      ≡
      false

    searchedLikelyLocalPaths :
      List String

    searchedLikelyLocalPathsAreRecorded :
      searchedLikelyLocalPaths
      ≡
      "/home/c/Downloads"
      ∷ "/home/c/Documents/code/dashi_agda/scripts/data/hepdata"
      ∷ "/home/c/Documents/code/dashi_agda/logs/research/provider_inputs"
      ∷ "/home/c/Documents/code/dashi_agda"
      ∷ []

    missingExpectedTableFiles :
      List String

    missingExpectedTableFilesAreRecorded :
      missingExpectedTableFiles
      ≡
      "/home/c/Downloads/HEPData-ins1486676-v1-Table_2.json"
      ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_2.yaml"
      ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_3.json"
      ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_3.yaml"
      ∷ "/home/c/Downloads/HEPData-ins1486676-v1.zip"
      ∷ "/home/c/Downloads/HEPData-ins1486676-v1-yaml.tar.gz"
      ∷ []

    concreteP5PrimeValueCovarianceTableSHA256 :
      String

    concreteP5PrimeValueCovarianceTableSHA256IsUnavailable :
      concreteP5PrimeValueCovarianceTableSHA256
      ≡
      "unavailable: no local table payload containing P5Prime values/covariance in q2 bins [4,6] and [6,8] was found"

    concreteNormalisedMomentCovarianceTableSHA256 :
      String

    concreteNormalisedMomentCovarianceTableSHA256IsCanonical :
      concreteNormalisedMomentCovarianceTableSHA256
      ≡
      "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"

open HEPDataIns1486676LocalSearchBinding public

canonicalHEPDataIns1486676LocalSearchBinding :
  HEPDataIns1486676LocalSearchBinding
canonicalHEPDataIns1486676LocalSearchBinding =
  mkHEPDataIns1486676LocalSearchBinding
    "/home/c/Downloads/ins1486676.json"
    refl
    "fc6f50bc02c70395fb1389888d47c873a8db56d0752cd340152ddf51844ebc85"
    refl
    "7834"
    refl
    "ins1486676 / HEPData 75193 v1"
    refl
    "https://www.hepdata.net/download/table/ins1486676/Table 1/json"
    refl
    "https://www.hepdata.net/download/table/ins1486676/Table 2/json"
    refl
    "https://www.hepdata.net/download/table/ins1486676/Table 3/json"
    refl
    "https://www.hepdata.net/record/data/75193/66907/1/0"
    refl
    "10.17182/hepdata.75193.v1"
    refl
    "10.17182/hepdata.75193.v1/t3"
    refl
    "scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json"
    refl
    "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"
    refl
    "258422"
    refl
    "1600"
    refl
    "Full covariance matrix of the normalised moments. The statistical and systematic uncertainties are combined."
    refl
    "1.1-6.0 GeV^2"
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ("/home/c/Downloads"
     ∷ "/home/c/Documents/code/dashi_agda/scripts/data/hepdata"
     ∷ "/home/c/Documents/code/dashi_agda/logs/research/provider_inputs"
     ∷ "/home/c/Documents/code/dashi_agda"
     ∷ [])
    refl
    ("/home/c/Downloads/HEPData-ins1486676-v1-Table_2.json"
     ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_2.yaml"
     ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_3.json"
     ∷ "/home/c/Downloads/HEPData-ins1486676-v1-Table_3.yaml"
     ∷ "/home/c/Downloads/HEPData-ins1486676-v1.zip"
     ∷ "/home/c/Downloads/HEPData-ins1486676-v1-yaml.tar.gz"
     ∷ [])
    refl
    "unavailable: no local table payload containing P5Prime values/covariance in q2 bins [4,6] and [6,8] was found"
    refl
    "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"
    refl

record HEPDataIns1486676RepoLocalArtifactBinding : Set where
  constructor mkHEPDataIns1486676RepoLocalArtifactBinding
  field
    recordJSONPath :
      String

    recordJSONPathIsRepoLocal :
      recordJSONPath
      ≡
      "scripts/data/hepdata/ins1486676/ins1486676-record.json"

    recordJSONSHA256 :
      String

    recordJSONSHA256IsRepoLocal :
      recordJSONSHA256
      ≡
      "94a6bb5aa212c87f25d23c19e67bf29a33c5d4dd7fa71f32a372c53ef980e62e"

    recordJSONSHA256Verified :
      Bool

    recordJSONSHA256VerifiedIsTrue :
      recordJSONSHA256Verified ≡ true

    recordJSONByteCount :
      String

    recordJSONByteCountIsRepoLocal :
      recordJSONByteCount
      ≡
      "7834"

    tableOneJSONPath :
      String

    tableOneJSONPathIsRepoLocal :
      tableOneJSONPath
      ≡
      "scripts/data/hepdata/ins1486676/table1-record-data-75193-66905.json"

    tableOneJSONSHA256 :
      String

    tableOneJSONSHA256IsRepoLocal :
      tableOneJSONSHA256
      ≡
      "a78ea64ac7be9099b435b80917922fe2f8423b9a29ff2a90b86bcdffabaa36bf"

    tableOneJSONByteCount :
      String

    tableOneJSONByteCountIsRepoLocal :
      tableOneJSONByteCount
      ≡
      "2790"

    tableOneDOI :
      String

    tableOneDOIIsCanonical :
      tableOneDOI
      ≡
      "10.17182/hepdata.75193.v1/t1"

    tableOneValueCount :
      String

    tableOneValueCountIsSix :
      tableOneValueCount
      ≡
      "6"

    tableThreeJSONPath :
      String

    tableThreeJSONPathIsRepoLocal :
      tableThreeJSONPath
      ≡
      "scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json"

    tableThreeJSONSHA256 :
      String

    tableThreeJSONSHA256IsRepoLocal :
      tableThreeJSONSHA256
      ≡
      "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"

    tableThreeJSONSHA256Verified :
      Bool

    tableThreeJSONSHA256VerifiedIsTrue :
      tableThreeJSONSHA256Verified ≡ true

    tableThreeJSONByteCount :
      String

    tableThreeJSONByteCountIsRepoLocal :
      tableThreeJSONByteCount
      ≡
      "258422"

    tableThreeDOI :
      String

    tableThreeDOIIsCanonical :
      tableThreeDOI
      ≡
      "10.17182/hepdata.75193.v1/t3"

    tableThreeValueCount :
      String

    tableThreeValueCountIsFortyByForty :
      tableThreeValueCount
      ≡
      "1600"

    tableThreeQ2Range :
      String

    tableThreeQ2RangeIsOnePointOneToSix :
      tableThreeQ2Range
      ≡
      "1.1-6.0 GeV^2"

    tableThreeDescription :
      String

    tableThreeDescriptionIsNormalisedMomentCovariance :
      tableThreeDescription
      ≡
      "Full covariance matrix of the normalised moments. The statistical and systematic uncertainties are combined."

    repoLocalTableChecksumBound :
      Bool

    repoLocalTableChecksumBoundIsTrue :
      repoLocalTableChecksumBound
      ≡
      true

    repoLocalBindingIsP5PrimeAngularValueCovariance :
      Bool

    repoLocalBindingIsP5PrimeAngularValueCovarianceIsFalse :
      repoLocalBindingIsP5PrimeAngularValueCovariance
      ≡
      false

open HEPDataIns1486676RepoLocalArtifactBinding public

canonicalHEPDataIns1486676RepoLocalArtifactBinding :
  HEPDataIns1486676RepoLocalArtifactBinding
canonicalHEPDataIns1486676RepoLocalArtifactBinding =
  mkHEPDataIns1486676RepoLocalArtifactBinding
    "scripts/data/hepdata/ins1486676/ins1486676-record.json"
    refl
    "94a6bb5aa212c87f25d23c19e67bf29a33c5d4dd7fa71f32a372c53ef980e62e"
    refl
    true
    refl
    "7834"
    refl
    "scripts/data/hepdata/ins1486676/table1-record-data-75193-66905.json"
    refl
    "a78ea64ac7be9099b435b80917922fe2f8423b9a29ff2a90b86bcdffabaa36bf"
    refl
    "2790"
    refl
    "10.17182/hepdata.75193.v1/t1"
    refl
    "6"
    refl
    "scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json"
    refl
    "d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"
    refl
    true
    refl
    "258422"
    refl
    "10.17182/hepdata.75193.v1/t3"
    refl
    "1600"
    refl
    "1.1-6.0 GeV^2"
    refl
    "Full covariance matrix of the normalised moments. The statistical and systematic uncertainties are combined."
    refl
    true
    refl
    false
    refl

record HEPDataRun12P5PrimeValueTableBinding : Set where
  constructor mkHEPDataRun12P5PrimeValueTableBinding
  field
    hepdataRecordDOI :
      String

    hepdataRecordDOIIsCurrentRun12 :
      hepdataRecordDOI
      ≡
      "10.17182/hepdata.167733.v1"

    hepdataTableDOI :
      String

    hepdataTableDOIIsConfig2 :
      hepdataTableDOI
      ≡
      "10.17182/hepdata.167733.v1/t2"

    inspireRecord :
      String

    inspireRecordIsFullRun12 :
      inspireRecord
      ≡
      "INSPIRE:3094698 / LHCb-PAPER-2025-041"

    tableName :
      String

    tableNameIsConfig2Results :
      tableName
      ≡
      "config_2_results"

    tableDescription :
      String

    tableDescriptionIsOptimisedPiBasis :
      tableDescription
      ≡
      "Fit configuration (ii): partially massive model, CP-asymmetries fixed to 0, optimised Pi basis, standard q2 binning"

    recordDataURL :
      String

    recordDataURLIsCanonical :
      recordDataURL
      ≡
      "https://www.hepdata.net/record/data/167733/1911073/1/0"

    localJSONPath :
      String

    localJSONPathIsRepoLocal :
      localJSONPath
      ≡
      "scripts/data/hepdata/ins3094698/table-config-2-results-record-data-167733-1911073.json"

    localJSONSHA256 :
      String

    localJSONSHA256IsCanonical :
      localJSONSHA256
      ≡
      "8ee74f4e774889eced2090fe60bbdaf681dd327dc1a349add992e038c7f62623"

    localJSONSHA256Verified :
      Bool

    localJSONSHA256VerifiedIsTrue :
      localJSONSHA256Verified ≡ true

    localJSONByteCount :
      String

    localJSONByteCountIsObserved :
      localJSONByteCount
      ≡
      "81622"

    q2BinCount :
      String

    q2BinCountIsTen :
      q2BinCount
      ≡
      "10"

    p5PrimeColumnHeader :
      String

    p5PrimeColumnHeaderIsCanonical :
      p5PrimeColumnHeader
      ≡
      "P5p [0.1]"

    p5PrimeFourToSixValue :
      String

    p5PrimeFourToSixValueIsObserved :
      p5PrimeFourToSixValue
      ≡
      "-4.79 in table units [0.1], i.e. -0.479"

    p5PrimeFourToSixStatSyst :
      String

    p5PrimeFourToSixStatSystIsObserved :
      p5PrimeFourToSixStatSyst
      ≡
      "stat -0.73/+0.73 and syst -0.07/+0.07 in table units [0.1]"

    p5PrimeSixToEightValue :
      String

    p5PrimeSixToEightValueIsObserved :
      p5PrimeSixToEightValue
      ≡
      "-5.86 in table units [0.1], i.e. -0.586"

    p5PrimeSixToEightStatSyst :
      String

    p5PrimeSixToEightStatSystIsObserved :
      p5PrimeSixToEightStatSyst
      ≡
      "stat -0.55/+0.55 and syst -0.06/+0.06 in table units [0.1]"

    totalCorrelationJSONPath :
      String

    totalCorrelationJSONPathIsRepoLocal :
      totalCorrelationJSONPath
      ≡
      "scripts/data/hepdata/ins3094698/config_2_correlation_total.json"

    totalCorrelationJSONSHA256 :
      String

    totalCorrelationJSONSHA256IsCanonical :
      totalCorrelationJSONSHA256
      ≡
      "d3ce138b3d7a3fe0a2777fe87ebe2e9161f14ff4d1ca66ff576d6e271a03c624"

    statisticalCorrelationJSONSHA256 :
      String

    statisticalCorrelationJSONSHA256IsCanonical :
      statisticalCorrelationJSONSHA256
      ≡
      "452a3252a6648dc1a0bd3d48907c271850f646c2c0339f07c8a151ab16edf5c0"

    systematicCorrelationJSONSHA256 :
      String

    systematicCorrelationJSONSHA256IsCanonical :
      systematicCorrelationJSONSHA256
      ≡
      "d15787e808c195ce4126483b6f7d524b49f718320728a06555c1cb4f3b05a7d8"

    artifactContainsP5PrimeValues :
      Bool

    artifactContainsP5PrimeValuesIsTrue :
      artifactContainsP5PrimeValues
      ≡
      true

    artifactContainsStatSystUncertainties :
      Bool

    artifactContainsStatSystUncertaintiesIsTrue :
      artifactContainsStatSystUncertainties
      ≡
      true

    artifactContainsFullCovarianceMatrix :
      Bool

    artifactContainsFullCovarianceMatrixIsTrue :
      artifactContainsFullCovarianceMatrix
      ≡
      true

    claimedHEPData89409Resolved :
      Bool

    claimedHEPData89409ResolvedIsFalse :
      claimedHEPData89409Resolved
      ≡
      false

open HEPDataRun12P5PrimeValueTableBinding public

canonicalHEPDataRun12P5PrimeValueTableBinding :
  HEPDataRun12P5PrimeValueTableBinding
canonicalHEPDataRun12P5PrimeValueTableBinding =
  mkHEPDataRun12P5PrimeValueTableBinding
    "10.17182/hepdata.167733.v1"
    refl
    "10.17182/hepdata.167733.v1/t2"
    refl
    "INSPIRE:3094698 / LHCb-PAPER-2025-041"
    refl
    "config_2_results"
    refl
    "Fit configuration (ii): partially massive model, CP-asymmetries fixed to 0, optimised Pi basis, standard q2 binning"
    refl
    "https://www.hepdata.net/record/data/167733/1911073/1/0"
    refl
    "scripts/data/hepdata/ins3094698/table-config-2-results-record-data-167733-1911073.json"
    refl
    "8ee74f4e774889eced2090fe60bbdaf681dd327dc1a349add992e038c7f62623"
    refl
    true
    refl
    "81622"
    refl
    "10"
    refl
    "P5p [0.1]"
    refl
    "-4.79 in table units [0.1], i.e. -0.479"
    refl
    "stat -0.73/+0.73 and syst -0.07/+0.07 in table units [0.1]"
    refl
    "-5.86 in table units [0.1], i.e. -0.586"
    refl
    "stat -0.55/+0.55 and syst -0.06/+0.06 in table units [0.1]"
    refl
    "scripts/data/hepdata/ins3094698/config_2_correlation_total.json"
    refl
    "d3ce138b3d7a3fe0a2777fe87ebe2e9161f14ff4d1ca66ff576d6e271a03c624"
    refl
    "452a3252a6648dc1a0bd3d48907c271850f646c2c0339f07c8a151ab16edf5c0"
    refl
    "d15787e808c195ce4126483b6f7d524b49f718320728a06555c1cb4f3b05a7d8"
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl

record LHCb2020P5PrimeValueTableArtifactBinding : Set where
  constructor mkLHCb2020P5PrimeValueTableArtifactBinding
  field
    paperIdentifier :
      String

    paperIdentifierIsRun2 :
      paperIdentifier
      ≡
      "LHCb-PAPER-2020-002 / arXiv:2003.04831 / INSPIRE:1784890 / CDS:2712641"

    sourcePage :
      String

    sourcePageIsLHCbPublic :
      sourcePage
      ≡
      "https://cern.ch/lhcbproject/Publications/p/LHCb-PAPER-2020-002.html"

    sourceTableIdentifier :
      String

    sourceTableIdentifierIsOptimisedObservableTable :
      sourceTableIdentifier
      ≡
      "LHCb public Table_2.pdf / TeX Table_1.tex / arXiv label tab:sub:piresults"

    localTeXPath :
      String

    localTeXPathIsRepoLocal :
      localTeXPath
      ≡
      "scripts/data/hepdata/ins1784890/lhcb-public-Table_1-optimised-observables.tex"

    localTeXSHA256 :
      String

    localTeXSHA256IsCanonical :
      localTeXSHA256
      ≡
      "bbc5f0e3a3fc3e705f61e170c671d075eaaa5370047d576fb75fc8257eb8ee6c"

    localTeXByteCount :
      String

    localTeXByteCountIsObserved :
      localTeXByteCount
      ≡
      "4586"

    supplementaryMeasurementsYAMLPath :
      String

    supplementaryMeasurementsYAMLPathIsRepoLocal :
      supplementaryMeasurementsYAMLPath
      ≡
      "scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/measurements.yml"

    supplementaryMeasurementsYAMLSHA256 :
      String

    supplementaryMeasurementsYAMLSHA256IsCanonical :
      supplementaryMeasurementsYAMLSHA256
      ≡
      "2be66f68d88c76b40ae0a04f277b8d3dbbfe1643c8da77dc65a9d661abd6dd7e"

    directP5PrimePlotMacroPath :
      String

    directP5PrimePlotMacroPathIsRepoLocal :
      directP5PrimePlotMacroPath
      ≡
      "scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/Fig3e-supp.C"

    directP5PrimePlotMacroSHA256 :
      String

    directP5PrimePlotMacroSHA256IsCanonical :
      directP5PrimePlotMacroSHA256
      ≡
      "f2c57fc9f3cdee6624fc562eee275f5308d2e94f43062e9a8a654f7f91afd6fe"

    p5PrimeFourToSixValue :
      String

    p5PrimeFourToSixValueIsObserved :
      p5PrimeFourToSixValue
      ≡
      "-0.439 +/- 0.111(stat) +/- 0.036(syst)"

    p5PrimeSixToEightValue :
      String

    p5PrimeSixToEightValueIsObserved :
      p5PrimeSixToEightValue
      ≡
      "-0.583 +/- 0.090(stat) +/- 0.030(syst)"

    p5PrimeValueArtifactBound :
      Bool

    p5PrimeValueArtifactBoundIsTrue :
      p5PrimeValueArtifactBound
      ≡
      true

    p5PrimeFullCovarianceMatrixBound :
      Bool

    p5PrimeFullCovarianceMatrixBoundIsFalse :
      p5PrimeFullCovarianceMatrixBound
      ≡
      false

    underlyingAngularCorrelationMatricesBound :
      Bool

    underlyingAngularCorrelationMatricesBoundIsTrue :
      underlyingAngularCorrelationMatricesBound
      ≡
      true

    hepdataDOIFamily89409Resolved :
      Bool

    hepdataDOIFamily89409ResolvedIsFalse :
      hepdataDOIFamily89409Resolved
      ≡
      false

open LHCb2020P5PrimeValueTableArtifactBinding public

canonicalLHCb2020P5PrimeValueTableArtifactBinding :
  LHCb2020P5PrimeValueTableArtifactBinding
canonicalLHCb2020P5PrimeValueTableArtifactBinding =
  mkLHCb2020P5PrimeValueTableArtifactBinding
    "LHCb-PAPER-2020-002 / arXiv:2003.04831 / INSPIRE:1784890 / CDS:2712641"
    refl
    "https://cern.ch/lhcbproject/Publications/p/LHCb-PAPER-2020-002.html"
    refl
    "LHCb public Table_2.pdf / TeX Table_1.tex / arXiv label tab:sub:piresults"
    refl
    "scripts/data/hepdata/ins1784890/lhcb-public-Table_1-optimised-observables.tex"
    refl
    "bbc5f0e3a3fc3e705f61e170c671d075eaaa5370047d576fb75fc8257eb8ee6c"
    refl
    "4586"
    refl
    "scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/measurements.yml"
    refl
    "2be66f68d88c76b40ae0a04f277b8d3dbbfe1643c8da77dc65a9d661abd6dd7e"
    refl
    "scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/Fig3e-supp.C"
    refl
    "f2c57fc9f3cdee6624fc562eee275f5308d2e94f43062e9a8a654f7f91afd6fe"
    refl
    "-0.439 +/- 0.111(stat) +/- 0.036(syst)"
    refl
    "-0.583 +/- 0.090(stat) +/- 0.030(syst)"
    refl
    true
    refl
    false
    refl
    true
    refl
    false
    refl

record LHCbP5PrimeHEPDataRouteBinding : Set where
  constructor mkLHCbP5PrimeHEPDataRouteBinding
  field
    claimedPrimaryRecord :
      String

    claimedPrimaryRecordIs160745 :
      claimedPrimaryRecord
      ≡
      "HEPData:160745"

    claimedPrimaryVersionedURL :
      String

    claimedPrimaryVersionedURLIsCanonical :
      claimedPrimaryVersionedURL
      ≡
      "https://www.hepdata.net/record/160745?version=1"

    claimedPrimarySubmissionYAMLURL :
      String

    claimedPrimarySubmissionYAMLURLIsCanonical :
      claimedPrimarySubmissionYAMLURL
      ≡
      "https://www.hepdata.net/record/160745/files/submission.yaml"

    claimedPrimaryResolvedMetadata :
      String

    claimedPrimaryResolvedMetadataIsIns2922449JetMass :
      claimedPrimaryResolvedMetadata
      ≡
      "resolved record metadata identifies HEPData:159893 / INSPIRE:2922449 heavy-flavour b-jet mass, not B0 -> K*0 mu+ mu- P5'"

    claimedPrimaryMatchesP5PrimeAngularLane :
      Bool

    claimedPrimaryMatchesP5PrimeAngularLaneIsFalse :
      claimedPrimaryMatchesP5PrimeAngularLane
      ≡
      false

    claimedPrimarySubmissionSHA256Bound :
      Bool

    claimedPrimarySubmissionSHA256BoundIsFalse :
      claimedPrimarySubmissionSHA256Bound
      ≡
      false

    fallbackRecord :
      String

    fallbackRecordIsIns1798504 :
      fallbackRecord
      ≡
      "HEPData:ins1798504"

    fallbackRecordDescription :
      String

    fallbackRecordDescriptionIsRun2Angular2020 :
      fallbackRecordDescription
      ≡
      "LHCb-PAPER-2020-002 / arXiv:2003.04831 Run 2 B0 -> K*0 mu+ mu- CP-averaged angular observables"

    fallbackMachineReadableRouteRecorded :
      Bool

    fallbackMachineReadableRouteRecordedIsTrue :
      fallbackMachineReadableRouteRecorded
      ≡
      true

    fallbackChecksumBoundHere :
      Bool

    fallbackChecksumBoundHereIsFalse :
      fallbackChecksumBoundHere
      ≡
      false

open LHCbP5PrimeHEPDataRouteBinding public

canonicalLHCbP5PrimeHEPDataRouteBinding :
  LHCbP5PrimeHEPDataRouteBinding
canonicalLHCbP5PrimeHEPDataRouteBinding =
  mkLHCbP5PrimeHEPDataRouteBinding
    "HEPData:160745"
    refl
    "https://www.hepdata.net/record/160745?version=1"
    refl
    "https://www.hepdata.net/record/160745/files/submission.yaml"
    refl
    "resolved record metadata identifies HEPData:159893 / INSPIRE:2922449 heavy-flavour b-jet mass, not B0 -> K*0 mu+ mu- P5'"
    refl
    false
    refl
    false
    refl
    "HEPData:ins1798504"
    refl
    "LHCb-PAPER-2020-002 / arXiv:2003.04831 Run 2 B0 -> K*0 mu+ mu- CP-averaged angular observables"
    refl
    true
    refl
    false
    refl

record SuppliedIns2922449Table16RejectionBinding : Set where
  constructor mkSuppliedIns2922449Table16RejectionBinding
  field
    suppliedLocalPath :
      String

    suppliedLocalPathIsCanonical :
      suppliedLocalPath
      ≡
      "/home/c/Downloads/HEPData-ins2922449-v1-Table_16.yaml"

    suppliedLocalSHA256 :
      String

    suppliedLocalSHA256IsCanonical :
      suppliedLocalSHA256
      ≡
      "47868e1936dc9f8b4bd20f2aa25ffe2350307737b346394d252d8c5b256ef256"

    suppliedJSONLocalPath :
      String

    suppliedJSONLocalPathIsCanonical :
      suppliedJSONLocalPath
      ≡
      "/home/c/Downloads/159893-1806203-1.json"

    suppliedJSONSHA256 :
      String

    suppliedJSONSHA256IsCanonical :
      suppliedJSONSHA256
      ≡
      "e182f28137dae0f43be0b99c11d728cd9509d09cc47f66cd64462a897738ea43"

    suppliedRecord :
      String

    suppliedRecordIsIns2922449 :
      suppliedRecord
      ≡
      "HEPData:ins2922449 / HEPData record 160745"

    suppliedTable :
      String

    suppliedTableIsTable16 :
      suppliedTable
      ≡
      "Table 16"

    suppliedObservable :
      String

    suppliedObservableIsJetMass :
      suppliedObservable
      ≡
      "normalized b-tagged jet mass distribution m_jet / p_T,jet"

    suppliedArtifactAcceptedForP5Prime :
      Bool

    suppliedArtifactAcceptedForP5PrimeIsFalse :
      suppliedArtifactAcceptedForP5Prime
      ≡
      false

open SuppliedIns2922449Table16RejectionBinding public

canonicalSuppliedIns2922449Table16RejectionBinding :
  SuppliedIns2922449Table16RejectionBinding
canonicalSuppliedIns2922449Table16RejectionBinding =
  mkSuppliedIns2922449Table16RejectionBinding
    "/home/c/Downloads/HEPData-ins2922449-v1-Table_16.yaml"
    refl
    "47868e1936dc9f8b4bd20f2aa25ffe2350307737b346394d252d8c5b256ef256"
    refl
    "/home/c/Downloads/159893-1806203-1.json"
    refl
    "e182f28137dae0f43be0b99c11d728cd9509d09cc47f66cd64462a897738ea43"
    refl
    "HEPData:ins2922449 / HEPData record 160745"
    refl
    "Table 16"
    refl
    "normalized b-tagged jet mass distribution m_jet / p_T,jet"
    refl
    false
    refl

record LHCbChecksumAcceptedResidualSurfaceReceipt : Setω where
  field
    checksumArtifactStatuses :
      List LHCbChecksumArtifactStatus

    checksumArtifactStatusesAreCanonical :
      checksumArtifactStatuses
      ≡
      canonicalLHCbChecksumArtifactStatuses

    acceptedResidualSurfaceStatuses :
      List LHCbAcceptedResidualSurfaceStatus

    acceptedResidualSurfaceStatusesAreCanonical :
      acceptedResidualSurfaceStatuses
      ≡
      canonicalLHCbAcceptedResidualSurfaceStatuses

    lhcbSupplementaryChecksumBinding :
      LHCbCDSSupplementaryChecksumBinding

    lhcbSupplementaryChecksumBindingIsCanonical :
      lhcbSupplementaryChecksumBinding
      ≡
      canonicalLHCbCDSSupplementaryChecksumBinding

    run12PublicResultBinding :
      LHCbP5PrimeRun12PublicResultBinding

    run12PublicResultBindingIsCanonical :
      run12PublicResultBinding
      ≡
      canonicalLHCbP5PrimeRun12PublicResultBinding

    p5PrimeHEPDataRouteBinding :
      LHCbP5PrimeHEPDataRouteBinding

    p5PrimeHEPDataRouteBindingIsCanonical :
      p5PrimeHEPDataRouteBinding
      ≡
      canonicalLHCbP5PrimeHEPDataRouteBinding

    suppliedIns2922449Table16RejectionBinding :
      SuppliedIns2922449Table16RejectionBinding

    suppliedIns2922449Table16RejectionBindingIsCanonical :
      suppliedIns2922449Table16RejectionBinding
      ≡
      canonicalSuppliedIns2922449Table16RejectionBinding

    hepdataIns1486676LocalSearchBinding :
      HEPDataIns1486676LocalSearchBinding

    hepdataIns1486676LocalSearchBindingIsCanonical :
      hepdataIns1486676LocalSearchBinding
      ≡
      canonicalHEPDataIns1486676LocalSearchBinding

    hepdataIns1486676RepoLocalArtifactBinding :
      HEPDataIns1486676RepoLocalArtifactBinding

    hepdataIns1486676RepoLocalArtifactBindingIsCanonical :
      hepdataIns1486676RepoLocalArtifactBinding
      ≡
      canonicalHEPDataIns1486676RepoLocalArtifactBinding

    hepdataRun12P5PrimeValueTableBinding :
      HEPDataRun12P5PrimeValueTableBinding

    hepdataRun12P5PrimeValueTableBindingIsCanonical :
      hepdataRun12P5PrimeValueTableBinding
      ≡
      canonicalHEPDataRun12P5PrimeValueTableBinding

    lhcb2020P5PrimeValueTableArtifactBinding :
      LHCb2020P5PrimeValueTableArtifactBinding

    lhcb2020P5PrimeValueTableArtifactBindingIsCanonical :
      lhcb2020P5PrimeValueTableArtifactBinding
      ≡
      canonicalLHCb2020P5PrimeValueTableArtifactBinding

    run12PublicResultRecorded :
      Bool

    run12PublicResultRecordedIsTrue :
      run12PublicResultRecorded
      ≡
      true

    claimedPrimaryHEPDataRecordAccepted :
      Bool

    claimedPrimaryHEPDataRecordAcceptedIsFalse :
      claimedPrimaryHEPDataRecordAccepted
      ≡
      false

    fallbackIns1798504RouteRecordedFlag :
      Bool

    fallbackIns1798504RouteRecordedFlagIsTrue :
      fallbackIns1798504RouteRecordedFlag
      ≡
      true

    lhcbChecksumBindingIsForSelectedThread :
      sourceCandidate lhcbSupplementaryChecksumBinding
      ≡
      Contract.lhcbPRD105012010CDS2779103

    lhcbChecksumDigestIsSupplementaryZip :
      payloadSHA256 lhcbSupplementaryChecksumBinding
      ≡
      "68bf6ab48ca104c2e37f1edeb64fbde59d4542600adf78c28869f092daef7fb8"

    selectedThreadSupplementaryChecksumPresent :
      Bool

    selectedThreadSupplementaryChecksumPresentIsTrue :
      selectedThreadSupplementaryChecksumPresent
      ≡
      true

    cernRepositoryRouteEvidencePresent :
      Bool

    cernRepositoryRouteEvidencePresentIsTrue :
      cernRepositoryRouteEvidencePresent
      ≡
      true

    cernRepositoryRouteIsValueCovarianceManifest :
      Bool

    cernRepositoryRouteIsValueCovarianceManifestIsFalse :
      cernRepositoryRouteIsValueCovarianceManifest
      ≡
      false

    hepdataIns2101841RecordResolvedHere :
      Bool

    hepdataIns2101841RecordResolvedHereIsFalse :
      hepdataIns2101841RecordResolvedHere
      ≡
      false

    hepdataIns2101841IsSelectedLHCbRecord :
      Bool

    hepdataIns2101841IsSelectedLHCbRecordIsFalse :
      hepdataIns2101841IsSelectedLHCbRecord
      ≡
      false

    selectedLHCbInspireRecord :
      String

    selectedLHCbInspireRecordIs1908217 :
      selectedLHCbInspireRecord
      ≡
      "1908217"

    hepdataValueTableChecksumReceiptPresent :
      Bool

    hepdataValueTableChecksumReceiptPresentIsTrue :
      hepdataValueTableChecksumReceiptPresent
      ≡
      true

    hepdataCovarianceTableChecksumReceiptPresent :
      Bool

    hepdataCovarianceTableChecksumReceiptPresentIsTrue :
      hepdataCovarianceTableChecksumReceiptPresent
      ≡
      true

    hepdataIns1486676NormalisedMomentTableChecksumBound :
      Bool

    hepdataIns1486676NormalisedMomentTableChecksumBoundIsTrue :
      hepdataIns1486676NormalisedMomentTableChecksumBound
      ≡
      true

    hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovariance :
      Bool

    hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovarianceIsFalse :
      hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovariance
      ≡
      false

    hepdataRun12P5PrimeValueTableChecksumBound :
      Bool

    hepdataRun12P5PrimeValueTableChecksumBoundIsTrue :
      hepdataRun12P5PrimeValueTableChecksumBound
      ≡
      true

    hepdataRun12P5PrimeFullCovarianceMatrixBound :
      Bool

    hepdataRun12P5PrimeFullCovarianceMatrixBoundIsTrue :
      hepdataRun12P5PrimeFullCovarianceMatrixBound
      ≡
      true

    lhcb2020P5PrimeValueTableArtifactBound :
      Bool

    lhcb2020P5PrimeValueTableArtifactBoundIsTrue :
      lhcb2020P5PrimeValueTableArtifactBound
      ≡
      true

    lhcb2020P5PrimeFullCovarianceMatrixBound :
      Bool

    lhcb2020P5PrimeFullCovarianceMatrixBoundIsFalse :
      lhcb2020P5PrimeFullCovarianceMatrixBound
      ≡
      false

    residualVectorArtifactPresent :
      Bool

    residualVectorArtifactPresentIsFalse :
      residualVectorArtifactPresent
      ≡
      false

    acceptedResidualCandidateConstructedHere :
      Bool

    acceptedResidualCandidateConstructedHereIsFalse :
      acceptedResidualCandidateConstructedHere
      ≡
      false

    p5PrimeResidualVectorComparison :
      Law.P5PrimeResidualVectorComparison

    p5PrimeResidualVectorComparisonIsCanonical :
      p5PrimeResidualVectorComparison
      ≡
      Law.canonicalP5PrimeResidualVectorComparison

    p5PrimeResidualVectorStatus :
      Law.P5PrimeResidualVectorStatus

    p5PrimeResidualVectorStatusIsBorderlineAnomalyCandidate :
      p5PrimeResidualVectorStatus
      ≡
      Law.p5PrimeBorderlineAnomalyCandidate

    p5PrimeResidualVectorAcceptedCandidateConstructedHere :
      Bool

    p5PrimeResidualVectorAcceptedCandidateConstructedHereIsFalse :
      p5PrimeResidualVectorAcceptedCandidateConstructedHere
      ≡
      false

    acceptedResidualSurfaceWhenPrerequisitesPresent :
      (prerequisites : Law.PenguinResidualAcceptedCandidatePrerequisites) →
      Residual.classifyResidualCandidate
        (Law.acceptedAuthorityState prerequisites)
        (Law.freezeState prerequisites)
        (Law.dataState prerequisites)
        (Law.theoryUncertaintyState prerequisites)
        Residual.sigmaAtMostTwo
      ≡
      Law.acceptedResidualCandidate

    blocker :
      List String

    sourceAndDigest :
      List String

open LHCbChecksumAcceptedResidualSurfaceReceipt public

canonicalLHCbChecksumAcceptedResidualSurfaceReceipt :
  LHCbChecksumAcceptedResidualSurfaceReceipt
canonicalLHCbChecksumAcceptedResidualSurfaceReceipt =
  record
    { checksumArtifactStatuses =
        canonicalLHCbChecksumArtifactStatuses
    ; checksumArtifactStatusesAreCanonical =
        refl
    ; acceptedResidualSurfaceStatuses =
        canonicalLHCbAcceptedResidualSurfaceStatuses
    ; acceptedResidualSurfaceStatusesAreCanonical =
        refl
    ; lhcbSupplementaryChecksumBinding =
        canonicalLHCbCDSSupplementaryChecksumBinding
    ; lhcbSupplementaryChecksumBindingIsCanonical =
        refl
    ; run12PublicResultBinding =
        canonicalLHCbP5PrimeRun12PublicResultBinding
    ; run12PublicResultBindingIsCanonical =
        refl
    ; p5PrimeHEPDataRouteBinding =
        canonicalLHCbP5PrimeHEPDataRouteBinding
    ; p5PrimeHEPDataRouteBindingIsCanonical =
        refl
    ; suppliedIns2922449Table16RejectionBinding =
        canonicalSuppliedIns2922449Table16RejectionBinding
    ; suppliedIns2922449Table16RejectionBindingIsCanonical =
        refl
    ; hepdataIns1486676LocalSearchBinding =
        canonicalHEPDataIns1486676LocalSearchBinding
    ; hepdataIns1486676LocalSearchBindingIsCanonical =
        refl
    ; hepdataIns1486676RepoLocalArtifactBinding =
        canonicalHEPDataIns1486676RepoLocalArtifactBinding
    ; hepdataIns1486676RepoLocalArtifactBindingIsCanonical =
        refl
    ; hepdataRun12P5PrimeValueTableBinding =
        canonicalHEPDataRun12P5PrimeValueTableBinding
    ; hepdataRun12P5PrimeValueTableBindingIsCanonical =
        refl
    ; lhcb2020P5PrimeValueTableArtifactBinding =
        canonicalLHCb2020P5PrimeValueTableArtifactBinding
    ; lhcb2020P5PrimeValueTableArtifactBindingIsCanonical =
        refl
    ; run12PublicResultRecorded =
        true
    ; run12PublicResultRecordedIsTrue =
        refl
    ; claimedPrimaryHEPDataRecordAccepted =
        false
    ; claimedPrimaryHEPDataRecordAcceptedIsFalse =
        refl
    ; fallbackIns1798504RouteRecordedFlag =
        true
    ; fallbackIns1798504RouteRecordedFlagIsTrue =
        refl
    ; lhcbChecksumBindingIsForSelectedThread =
        refl
    ; lhcbChecksumDigestIsSupplementaryZip =
        refl
    ; selectedThreadSupplementaryChecksumPresent =
        true
    ; selectedThreadSupplementaryChecksumPresentIsTrue =
        refl
    ; cernRepositoryRouteEvidencePresent =
        true
    ; cernRepositoryRouteEvidencePresentIsTrue =
        refl
    ; cernRepositoryRouteIsValueCovarianceManifest =
        false
    ; cernRepositoryRouteIsValueCovarianceManifestIsFalse =
        refl
    ; hepdataIns2101841RecordResolvedHere =
        false
    ; hepdataIns2101841RecordResolvedHereIsFalse =
        refl
    ; hepdataIns2101841IsSelectedLHCbRecord =
        false
    ; hepdataIns2101841IsSelectedLHCbRecordIsFalse =
        refl
    ; selectedLHCbInspireRecord =
        "1908217"
    ; selectedLHCbInspireRecordIs1908217 =
        refl
    ; hepdataValueTableChecksumReceiptPresent =
        true
    ; hepdataValueTableChecksumReceiptPresentIsTrue =
        refl
    ; hepdataCovarianceTableChecksumReceiptPresent =
        true
    ; hepdataCovarianceTableChecksumReceiptPresentIsTrue =
        refl
    ; hepdataIns1486676NormalisedMomentTableChecksumBound =
        true
    ; hepdataIns1486676NormalisedMomentTableChecksumBoundIsTrue =
        refl
    ; hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovariance =
        false
    ; hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovarianceIsFalse =
        refl
    ; hepdataRun12P5PrimeValueTableChecksumBound =
        true
    ; hepdataRun12P5PrimeValueTableChecksumBoundIsTrue =
        refl
    ; hepdataRun12P5PrimeFullCovarianceMatrixBound =
        true
    ; hepdataRun12P5PrimeFullCovarianceMatrixBoundIsTrue =
        refl
    ; lhcb2020P5PrimeValueTableArtifactBound =
        true
    ; lhcb2020P5PrimeValueTableArtifactBoundIsTrue =
        refl
    ; lhcb2020P5PrimeFullCovarianceMatrixBound =
        false
    ; lhcb2020P5PrimeFullCovarianceMatrixBoundIsFalse =
        refl
    ; residualVectorArtifactPresent =
        false
    ; residualVectorArtifactPresentIsFalse =
        refl
    ; acceptedResidualCandidateConstructedHere =
        false
    ; acceptedResidualCandidateConstructedHereIsFalse =
        refl
    ; p5PrimeResidualVectorComparison =
        Law.canonicalP5PrimeResidualVectorComparison
    ; p5PrimeResidualVectorComparisonIsCanonical =
        refl
    ; p5PrimeResidualVectorStatus =
        Law.p5PrimeBorderlineAnomalyCandidate
    ; p5PrimeResidualVectorStatusIsBorderlineAnomalyCandidate =
        refl
    ; p5PrimeResidualVectorAcceptedCandidateConstructedHere =
        false
    ; p5PrimeResidualVectorAcceptedCandidateConstructedHereIsFalse =
        refl
    ; acceptedResidualSurfaceWhenPrerequisitesPresent =
        Law.acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent
          Law.canonicalPenguinDecayResidualComparisonLaw
    ; blocker =
        "2025 LHCb public result LHCb-PAPER-2025-041 / arXiv:2512.18053 / CDS:2951844 records the full Run 1+2 B0 -> K*0 mu+ mu- angular-analysis target with 8.4 fb^-1 and public 4 sigma global-fit tension, but it is not bound here as an accepted HEPData checksum receipt"
        ∷ "Claimed primary HEPData record 160745 was checked here and resolves to HEPData:159893 / INSPIRE:2922449 heavy-flavour b-jet mass metadata, not the P5' angular-observable lane"
        ∷ "The supplied local Table 16 YAML files all hash to 47868e1936dc9f8b4bd20f2aa25ffe2350307737b346394d252d8c5b256ef256 and encode normalized b-tagged jet mass m_jet / p_T,jet, so they are rejected for P5'"
        ∷ "The supplied local JSON /home/c/Downloads/159893-1806203-1.json hashes to e182f28137dae0f43be0b99c11d728cd9509d09cc47f66cd64462a897738ea43 and describes the same HEPData:159893.v1/t17 b-jet mass Table 16, so it is rejected for P5'"
        ∷ "Fallback route HEPData:ins1798504 / LHCb-PAPER-2020-002 / arXiv:2003.04831 was rechecked and returned 404 from the browser route; the claimed DOI family 10.17182/hepdata.89409 did not resolve through doi.org"
        ∷ "Requested 2020 P5' value artifact is bound from LHCb/CDS/arXiv TeX, not HEPData: scripts/data/hepdata/ins1784890/lhcb-public-Table_1-optimised-observables.tex, sha256 bbc5f0e3a3fc3e705f61e170c671d075eaaa5370047d576fb75fc8257eb8ee6c"
        ∷ "The 2020 supplementary measurements.yml artifact is bound with sha256 2be66f68d88c76b40ae0a04f277b8d3dbbfe1643c8da77dc65a9d661abd6dd7e; it carries underlying FL/S_i/AFB correlation matrices, not a direct P5' covariance matrix"
        ∷ "The 2020 TeX table gives P5' [4,6] = -0.439 +/- 0.111(stat) +/- 0.036(syst) and [6,8] = -0.583 +/- 0.090(stat) +/- 0.030(syst); no full covariance matrix is bound from that route"
        ∷ "Reachable P5' value-table route is the current full Run 1+2 LHCb record 10.17182/hepdata.167733.v1/t2, local JSON scripts/data/hepdata/ins3094698/table-config-2-results-record-data-167733-1911073.json, sha256 8ee74f4e774889eced2090fe60bbdaf681dd327dc1a349add992e038c7f62623"
        ∷ "HEPData t2 config_2_results contains the optimised Pi-basis P5p column with stat/syst uncertainty fields in q2 bins [4,6] and [6,8]; it does not expose a full covariance matrix table"
        ∷ "Checksum is now obtained for the current HEPData P5' value table, total/stat/syst correlation resources, and the CDS supplementary archive"
        ∷ "CERN repository route https://repository.cern/records/5r7hz-c7e34 records the quoted branching-fraction value as thesis route evidence, not as a HEPData value/covariance manifest"
        ∷ "Direct HEPData route https://www.hepdata.net/record/ins2101841 returned HTTP 404 here; INSPIRE record 2101841 is unrelated to the selected LHCb paper"
        ∷ "The selected 2021 LHCb DOI resolves through INSPIRE as record 1908217; the current full Run 1+2 HEPData value-table route resolves separately through INSPIRE record 3094698"
        ∷ "The verified CDS supplementary ZIP contains supplementary.pdf, supplementary.tex, README, and figure assets only; it is not a value/covariance manifest"
        ∷ "HEPData ins1486676 / 10.17182/hepdata.75193.v1 resolves to the 2016 B0 -> K+ pi- mu+ mu- normalised-moment analysis, not the B0 -> K*0 mu+ mu- P5' angular-analysis table"
        ∷ "HEPData Table 3 / 10.17182/hepdata.75193.v1/t3 is bound here as the normalised-moment covariance artifact: scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json, sha256 d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e, 1600 entries"
        ∷ "Repo-local B1 artifact facts consumed here: scripts/data/hepdata/ins1486676/ins1486676-record.json sha256 94a6bb5aa212c87f25d23c19e67bf29a33c5d4dd7fa71f32a372c53ef980e62e; table1 sha256 a78ea64ac7be9099b435b80917922fe2f8423b9a29ff2a90b86bcdffabaa36bf; table3 sha256 d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"
        ∷ "The repo-local ins1486676 binding is accepted only as a checksum/table binding for normalised-moment artifacts, not as a P5' angular value/covariance table"
        ∷ "Direct YAML/table download endpoints returned a Cloudflare challenge in this environment; the bound payload is the HEPData record-data JSON endpoint https://www.hepdata.net/record/data/75193/66907/1/0"
        ∷ "Remaining needed artifact: full covariance matrix, if Gate 5 insists on covariance whitening rather than the value table's stat/syst uncertainty fields"
        ∷ "Needed residual artifact: frozen residual vector JSON or equivalent projection output bound to the LHCb checksum, SM baseline digest, Wilson authority digest, CKM source, projection-code freeze hash, and no-posterior-tuning attestation"
        ∷ "Gate 5 P5' residual vector comparison consumes the canonical checksum value already in this receipt and applies r = (obs - SM) / sqrt(stat^2 + syst^2 + th^2) for q2 bins [4,6] and [6,8]"
        ∷ "Residual vector status is borderline/anomaly candidate from published signed pulls [4,6] = -2.8 sigma and [6,8] = -3.0 sigma; acceptedResidualCandidate remains false here"
        ∷ "Exact source checked: https://cds.cern.ch/record/2779103/files/LHCb-PAPER-2021-008-supplementary.zip?version=1"
        ∷ "Exact publication page checked: https://cern.ch/lhcbproject/Publications/p/LHCb-PAPER-2021-008.html"
        ∷ "HEPData search route exposed record 10.17182/hepdata.167733.v1 and table t2 through the browser record-data endpoint; CLI routes remain intermittently Cloudflare-gated"
        ∷ []
    ; sourceAndDigest =
        "2025 public LHCb result: LHCb-PAPER-2025-041 / arXiv:2512.18053 / CDS:2951844"
        ∷ "2025 public LHCb result URL: https://cds.cern.ch/record/2951844?ln=en"
        ∷ "2025 public-result dataset: 8.4 fb^-1 from 2011, 2012, and 2016-2018 LHCb data"
        ∷ "Claimed primary HEPData record checked: https://www.hepdata.net/record/160745?version=1"
        ∷ "Claimed primary route result: mismatched HEPData:159893 / INSPIRE:2922449 b-jet mass record; no P5' submission.yaml checksum accepted"
        ∷ "Rejected local artifact: /home/c/Downloads/HEPData-ins2922449-v1-Table_16.yaml"
        ∷ "Rejected local artifact sha256: 47868e1936dc9f8b4bd20f2aa25ffe2350307737b346394d252d8c5b256ef256"
        ∷ "Rejected local JSON artifact: /home/c/Downloads/159893-1806203-1.json"
        ∷ "Rejected local JSON artifact sha256: e182f28137dae0f43be0b99c11d728cd9509d09cc47f66cd64462a897738ea43"
        ∷ "Fallback machine-readable route attempted: https://www.hepdata.net/record/ins1798504 -> 404 in browser"
        ∷ "Claimed DOI family attempted: https://doi.org/10.17182/hepdata.89409 -> DOI not found"
        ∷ "Bound 2020 P5' value table source: LHCb-PAPER-2020-002 / arXiv:2003.04831 / INSPIRE:1784890 / CDS:2712641"
        ∷ "Bound 2020 P5' value table local file: scripts/data/hepdata/ins1784890/lhcb-public-Table_1-optimised-observables.tex"
        ∷ "Bound 2020 P5' value table sha256: bbc5f0e3a3fc3e705f61e170c671d075eaaa5370047d576fb75fc8257eb8ee6c"
        ∷ "Bound 2020 supplementary measurements.yml local file: scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/measurements.yml"
        ∷ "Bound 2020 supplementary measurements.yml sha256: 2be66f68d88c76b40ae0a04f277b8d3dbbfe1643c8da77dc65a9d661abd6dd7e"
        ∷ "Bound 2020 direct P5' plot macro local file: scripts/data/hepdata/lhcb_prl125_011802_arxiv2003_04831/extracted/Fig3e-supp.C"
        ∷ "Bound 2020 direct P5' plot macro sha256: f2c57fc9f3cdee6624fc562eee275f5308d2e94f43062e9a8a654f7f91afd6fe"
        ∷ "Bound 2020 P5' [4,6]: -0.439 +/- 0.111(stat) +/- 0.036(syst)"
        ∷ "Bound 2020 P5' [6,8]: -0.583 +/- 0.090(stat) +/- 0.030(syst)"
        ∷ "Bound P5' HEPData record DOI: 10.17182/hepdata.167733.v1"
        ∷ "Bound P5' HEPData table DOI: 10.17182/hepdata.167733.v1/t2"
        ∷ "Bound P5' HEPData table data URL: https://www.hepdata.net/record/data/167733/1911073/1/0"
        ∷ "Bound P5' HEPData table local file: scripts/data/hepdata/ins3094698/table-config-2-results-record-data-167733-1911073.json"
        ∷ "Bound P5' HEPData table sha256: 8ee74f4e774889eced2090fe60bbdaf681dd327dc1a349add992e038c7f62623"
        ∷ "Bound P5' HEPData table byte count: 81622"
        ∷ "Bound P5' HEPData total correlation JSON sha256: d3ce138b3d7a3fe0a2777fe87ebe2e9161f14ff4d1ca66ff576d6e271a03c624"
        ∷ "Bound P5' HEPData statistical correlation JSON sha256: 452a3252a6648dc1a0bd3d48907c271850f646c2c0339f07c8a151ab16edf5c0"
        ∷ "Bound P5' HEPData systematic correlation JSON sha256: d15787e808c195ce4126483b6f7d524b49f718320728a06555c1cb4f3b05a7d8"
        ∷ "Bound P5' HEPData P5p [4,6]: -4.79 in [0.1] table units, stat -0.73/+0.73, syst -0.07/+0.07"
        ∷ "Bound P5' HEPData P5p [6,8]: -5.86 in [0.1] table units, stat -0.55/+0.55, syst -0.06/+0.06"
        ∷ "CDS record: https://cds.cern.ch/record/2779103"
        ∷ "Publication DOI: 10.1103/PhysRevD.105.012010"
        ∷ "LHCb report: LHCb-PAPER-2021-008"
        ∷ "Supplementary archive URL: https://cds.cern.ch/record/2779103/files/LHCb-PAPER-2021-008-supplementary.zip?version=1"
        ∷ "Supplementary archive sha256: 68bf6ab48ca104c2e37f1edeb64fbde59d4542600adf78c28869f092daef7fb8"
        ∷ "Gate 5 P5' residual law: r = (obs - SM) / sqrt(stat^2 + syst^2 + th^2)"
        ∷ "Gate 5 P5' residual vector: [4,6] -> -2.8 sigma; [6,8] -> -3.0 sigma; status borderline/anomaly candidate; acceptedResidualCandidate false"
        ∷ "Supplementary archive size from CDS metadata: 6284402 bytes"
        ∷ "Supplementary ZIP listing checked: README, supplementary.pdf, supplementary.tex, figs/*.C, figs/*.pdf, figs/*.eps, figs/*.png"
        ∷ "supplementary.tex sha256 from downloaded ZIP: 734c1bf0292bcf36b9954df8a32eb331092aa1c7d8792bea732d8b5521d52e67"
        ∷ "supplementary.pdf sha256 from downloaded ZIP: 9f6be4a41e82ac81887c3ffeb4e83824c4e95a0d00e29d19fef254f8ec966373"
        ∷ "CERN repository route evidence: https://repository.cern/records/5r7hz-c7e34"
        ∷ "Unrelated route attempted: https://www.hepdata.net/record/ins2101841; INSPIRE 2101841 is not LHCb-PAPER-2021-008"
        ∷ "Selected LHCb INSPIRE record: https://inspirehep.net/api/literature/1908217"
        ∷ "INSPIRE 1908217 metadata sha256 as fetched here: 7f2f72d4b27757d1ea463f7dcab5053788dd20cab188722494128962901330a5"
        ∷ "HEPData ins1486676 record DOI: 10.17182/hepdata.75193.v1"
        ∷ "HEPData ins1486676 covariance table DOI: 10.17182/hepdata.75193.v1/t3"
        ∷ "HEPData ins1486676 covariance table local file: scripts/data/hepdata/ins1486676/table3-record-data-75193-66907.json"
        ∷ "HEPData ins1486676 covariance table sha256: d05fbdf6195b4ae625b505f0bc609f11a718e666825f9e8385d3c3878ded7e5e"
        ∷ "HEPData ins1486676 covariance table byte count: 258422"
        ∷ "HEPData ins1486676 covariance table entry count: 1600"
        ∷ "HEPData ins1486676 repo-local record JSON sha256: 94a6bb5aa212c87f25d23c19e67bf29a33c5d4dd7fa71f32a372c53ef980e62e"
        ∷ "HEPData ins1486676 repo-local Table 1 JSON sha256: a78ea64ac7be9099b435b80917922fe2f8423b9a29ff2a90b86bcdffabaa36bf"
        ∷ []
    }

canonicalLHCbSelectedThreadChecksumAuthorityPresent :
  selectedThreadSupplementaryChecksumPresent
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  true
canonicalLHCbSelectedThreadChecksumAuthorityPresent =
  refl

canonicalLHCbAcceptedResidualCandidateNotConstructedHere :
  acceptedResidualCandidateConstructedHere
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  false
canonicalLHCbAcceptedResidualCandidateNotConstructedHere =
  refl

canonicalLHCbP5PrimeResidualVectorStatus :
  p5PrimeResidualVectorStatus
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  Law.p5PrimeBorderlineAnomalyCandidate
canonicalLHCbP5PrimeResidualVectorStatus =
  refl

canonicalLHCbP5PrimeResidualVectorAcceptedCandidateNotConstructedHere :
  p5PrimeResidualVectorAcceptedCandidateConstructedHere
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  false
canonicalLHCbP5PrimeResidualVectorAcceptedCandidateNotConstructedHere =
  refl

canonicalLHCbIns1486676NormalisedMomentChecksumBound :
  hepdataIns1486676NormalisedMomentTableChecksumBound
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  true
canonicalLHCbIns1486676NormalisedMomentChecksumBound =
  refl

canonicalLHCbIns1486676NormalisedMomentNotP5PrimeAngularValueCovariance :
  hepdataIns1486676NormalisedMomentBindingIsP5PrimeAngularValueCovariance
    canonicalLHCbChecksumAcceptedResidualSurfaceReceipt
  ≡
  false
canonicalLHCbIns1486676NormalisedMomentNotP5PrimeAngularValueCovariance =
  refl
