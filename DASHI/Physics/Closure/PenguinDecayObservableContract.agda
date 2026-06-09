module DASHI.Physics.Closure.PenguinDecayObservableContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as R
import DASHI.Core.AuthorityBoundary as Authority

------------------------------------------------------------------------
-- b -> s mu+ mu- observable contract.
--
-- This is a concrete, finite, non-promoting observable contract for the
-- selected rare-penguin empirical thread lane.  It selects bToSLeptonPair
-- from the projection-defect receipt and records only the observable surfaces
-- needed to use that lane as an indirect projection-defect detector.  It does
-- not construct a calibrated empirical receipt, an accepted authority token,
-- or a non-SM promotion.

data PenguinObservableContractStatus : Set where
  concreteBToSMuonPairProjectionDefectObservableNonPromoting :
    PenguinObservableContractStatus

data LeptonPairChannel : Set where
  muonPair :
    LeptonPairChannel

data PenguinObservableKind : Set where
  branchingRatio :
    PenguinObservableKind
  angularCoefficient :
    PenguinObservableKind
  cpAsymmetry :
    PenguinObservableKind

canonicalPenguinObservableKinds :
  List PenguinObservableKind
canonicalPenguinObservableKinds =
  branchingRatio
  ∷ angularCoefficient
  ∷ cpAsymmetry
  ∷ []

kindToReceiptObservable :
  PenguinObservableKind →
  R.IndirectObservable
kindToReceiptObservable branchingRatio =
  R.branchingRatioDeviation
kindToReceiptObservable angularCoefficient =
  R.angularCoefficientDeviation
kindToReceiptObservable cpAsymmetry =
  R.cpAsymmetryDeviation

canonicalPenguinReceipt :
  R.PenguinDecayProjectionDefectReceipt
canonicalPenguinReceipt =
  R.canonicalPenguinDecayProjectionDefectReceipt

selectedCanonicalTarget :
  R.RarePenguinDecay
selectedCanonicalTarget =
  R.bToSLeptonPair

selectedTargetIsBToSLeptonPair :
  selectedCanonicalTarget ≡ R.bToSLeptonPair
selectedTargetIsBToSLeptonPair =
  refl

selectedTargetSourceIsBottom :
  R.decaySourceFlavour selectedCanonicalTarget ≡ R.bottom
selectedTargetSourceIsBottom =
  refl

data ObservableUnitConvention : Set where
  dimensionlessRatio :
    ObservableUnitConvention
  gevSquaredBinAxis :
    ObservableUnitConvention
  signedAsymmetryUnit :
    ObservableUnitConvention

unitConvention :
  PenguinObservableKind →
  ObservableUnitConvention
unitConvention branchingRatio =
  dimensionlessRatio
unitConvention angularCoefficient =
  dimensionlessRatio
unitConvention cpAsymmetry =
  signedAsymmetryUnit

data ObservableNormalization : Set where
  totalDecayWidthNormalized :
    ObservableNormalization
  angularBasisNormalized :
    ObservableNormalization
  particleAntiparticleDifferenceOverSum :
    ObservableNormalization

normalizationConvention :
  PenguinObservableKind →
  ObservableNormalization
normalizationConvention branchingRatio =
  totalDecayWidthNormalized
normalizationConvention angularCoefficient =
  angularBasisNormalized
normalizationConvention cpAsymmetry =
  particleAntiparticleDifferenceOverSum

data ObservableBinning : Set where
  qSquaredWindow :
    ObservableBinning
  angularBasisBin :
    ObservableBinning
  decayModeIntegratedBin :
    ObservableBinning

binningConvention :
  PenguinObservableKind →
  ObservableBinning
binningConvention branchingRatio =
  qSquaredWindow
binningConvention angularCoefficient =
  angularBasisBin
binningConvention cpAsymmetry =
  decayModeIntegratedBin

record PenguinObservableDescriptor : Set where
  constructor mkPenguinObservableDescriptor
  field
    observableKind :
      PenguinObservableKind

    receiptObservable :
      R.IndirectObservable

    receiptObservableMatchesKind :
      receiptObservable ≡ kindToReceiptObservable observableKind

    unit :
      ObservableUnitConvention

    unitMatchesKind :
      unit ≡ unitConvention observableKind

    unitLabel :
      String

    normalization :
      ObservableNormalization

    normalizationMatchesKind :
      normalization ≡ normalizationConvention observableKind

    normalizationLabel :
      String

    binning :
      ObservableBinning

    binningMatchesKind :
      binning ≡ binningConvention observableKind

    binningLabel :
      String

    authorityRequired :
      Bool

    authorityRequiredIsTrue :
      authorityRequired ≡ true

    authorityRequiredFields :
      List String

open PenguinObservableDescriptor public

branchingRatioDescriptor :
  PenguinObservableDescriptor
branchingRatioDescriptor =
  mkPenguinObservableDescriptor
    branchingRatio
    R.branchingRatioDeviation
    refl
    dimensionlessRatio
    refl
    "dimensionless branching fraction"
    totalDecayWidthNormalized
    refl
    "partial decay width divided by total parent-hadron decay width"
    qSquaredWindow
    refl
    "dimuon invariant-mass-squared q^2 window with stated edge convention"
    true
    refl
    ( "experiment/collaboration"
      ∷ "decay channel and final-state reconstruction"
      ∷ "q^2 bin edges and veto windows"
      ∷ "branching-fraction normalization channel or absolute normalization"
      ∷ "statistical and systematic uncertainty model"
      ∷ [] )

angularCoefficientDescriptor :
  PenguinObservableDescriptor
angularCoefficientDescriptor =
  mkPenguinObservableDescriptor
    angularCoefficient
    R.angularCoefficientDeviation
    refl
    dimensionlessRatio
    refl
    "dimensionless angular coefficient"
    angularBasisNormalized
    refl
    "coefficient in the declared angular basis and folding convention"
    angularBasisBin
    refl
    "q^2 bin plus declared angular basis, folding, and acceptance convention"
    true
    refl
    ( "experiment/collaboration"
      ∷ "angular basis definition"
      ∷ "q^2 bin edges and resonance vetoes"
      ∷ "acceptance and efficiency correction convention"
      ∷ "covariance or correlation matrix"
      ∷ [] )

cpAsymmetryDescriptor :
  PenguinObservableDescriptor
cpAsymmetryDescriptor =
  mkPenguinObservableDescriptor
    cpAsymmetry
    R.cpAsymmetryDeviation
    refl
    signedAsymmetryUnit
    refl
    "dimensionless signed CP asymmetry"
    particleAntiparticleDifferenceOverSum
    refl
    "(rate anti-particle minus rate particle) divided by their sum, with sign convention stated"
    decayModeIntegratedBin
    refl
    "declared decay-mode and q^2 integration region"
    true
    refl
    ( "experiment/collaboration"
      ∷ "particle and anti-particle tagging convention"
      ∷ "CP-asymmetry sign convention"
      ∷ "decay-mode and q^2 integration region"
      ∷ "production/detection asymmetry correction convention"
      ∷ [] )

canonicalPenguinObservableDescriptors :
  List PenguinObservableDescriptor
canonicalPenguinObservableDescriptors =
  branchingRatioDescriptor
  ∷ angularCoefficientDescriptor
  ∷ cpAsymmetryDescriptor
  ∷ []

descriptorForKind :
  PenguinObservableKind →
  PenguinObservableDescriptor
descriptorForKind branchingRatio =
  branchingRatioDescriptor
descriptorForKind angularCoefficient =
  angularCoefficientDescriptor
descriptorForKind cpAsymmetry =
  cpAsymmetryDescriptor

descriptorWitness :
  PenguinObservableDescriptor →
  R.IndirectWitness
descriptorWitness descriptor =
  R.PenguinDecayProjectionDefectReceipt.witnessExtractor
    canonicalPenguinReceipt
    selectedCanonicalTarget
    (receiptObservable descriptor)

descriptorWitnessIsIndirect :
  (descriptor : PenguinObservableDescriptor) →
  R.extractionMode (descriptorWitness descriptor)
  ≡
  R.indirectProjectionDefectExtraction
descriptorWitnessIsIndirect descriptor =
  R.PenguinDecayProjectionDefectReceipt.witnessExtractorIsIndirect
    canonicalPenguinReceipt
    selectedCanonicalTarget
    (receiptObservable descriptor)

descriptorWitnessReturnsSMProjection :
  (descriptor : PenguinObservableDescriptor) →
  R.projectedAmplitude (descriptorWitness descriptor)
  ≡
  R.standardModelSurface
descriptorWitnessReturnsSMProjection descriptor =
  R.PenguinDecayProjectionDefectReceipt.witnessExtractorReturnsSMProjection
    canonicalPenguinReceipt
    selectedCanonicalTarget
    (receiptObservable descriptor)

descriptorWitnessReturnsResidualDefect :
  (descriptor : PenguinObservableDescriptor) →
  R.extractedDefect (descriptorWitness descriptor)
  ≡
  R.residualDefectSurface
descriptorWitnessReturnsResidualDefect descriptor =
  R.PenguinDecayProjectionDefectReceipt.witnessExtractorReturnsResidualDefect
    canonicalPenguinReceipt
    selectedCanonicalTarget
    (receiptObservable descriptor)

data PenguinObservableAuthorityField : Set where
  requiredExperimentIdentifier :
    PenguinObservableAuthorityField
  requiredPublicRecordIdentifier :
    PenguinObservableAuthorityField
  requiredDecayModeDefinition :
    PenguinObservableAuthorityField
  requiredObservableDefinition :
    PenguinObservableAuthorityField
  requiredUnitAndNormalizationConvention :
    PenguinObservableAuthorityField
  requiredBinningConvention :
    PenguinObservableAuthorityField
  requiredUncertaintyAndCovarianceSemantics :
    PenguinObservableAuthorityField
  requiredDigestOrStableCitation :
    PenguinObservableAuthorityField

canonicalAuthorityRequiredFields :
  List PenguinObservableAuthorityField
canonicalAuthorityRequiredFields =
  requiredExperimentIdentifier
  ∷ requiredPublicRecordIdentifier
  ∷ requiredDecayModeDefinition
  ∷ requiredObservableDefinition
  ∷ requiredUnitAndNormalizationConvention
  ∷ requiredBinningConvention
  ∷ requiredUncertaintyAndCovarianceSemantics
  ∷ requiredDigestOrStableCitation
  ∷ []

canonicalAuthorityRequiredFieldNames :
  List String
canonicalAuthorityRequiredFieldNames =
  "experimentIdentifier"
  ∷ "publicRecordIdentifier"
  ∷ "decayModeDefinition"
  ∷ "observableDefinition"
  ∷ "unitAndNormalizationConvention"
  ∷ "binningConvention"
  ∷ "uncertaintyAndCovarianceSemantics"
  ∷ "digestOrStableCitation"
  ∷ []

data DatasetAuthorityNamespace : Set where
  cernCDSRecord :
    DatasetAuthorityNamespace
  journalDOIRecord :
    DatasetAuthorityNamespace
  hepDataStyleRecord :
    DatasetAuthorityNamespace

canonicalDatasetAuthorityNamespaces :
  List DatasetAuthorityNamespace
canonicalDatasetAuthorityNamespaces =
  cernCDSRecord
  ∷ journalDOIRecord
  ∷ hepDataStyleRecord
  ∷ []

data HEPDataTableBindingField : Set where
  hepDataRecordIdentifierField :
    HEPDataTableBindingField
  hepDataTableIdentifierField :
    HEPDataTableBindingField
  hepDataPayloadFileField :
    HEPDataTableBindingField
  hepDataPayloadChecksumField :
    HEPDataTableBindingField
  hepDataChecksumAuthorityField :
    HEPDataTableBindingField

canonicalHEPDataTableBindingFields :
  List HEPDataTableBindingField
canonicalHEPDataTableBindingFields =
  hepDataRecordIdentifierField
  ∷ hepDataTableIdentifierField
  ∷ hepDataPayloadFileField
  ∷ hepDataPayloadChecksumField
  ∷ hepDataChecksumAuthorityField
  ∷ []

data HEPDataChecksumAuthorityStatus : Set where
  checksumAuthorityMissingFailClosed :
    HEPDataChecksumAuthorityStatus

data PenguinDatasetSourceCandidateName : Set where
  cmsHEPData135675ResultsTable :
    PenguinDatasetSourceCandidateName
  lhcbBsMuMuCERN5r7hzC7e34 :
    PenguinDatasetSourceCandidateName

lhcbPRD105012010CDS2779103 :
  PenguinDatasetSourceCandidateName
lhcbPRD105012010CDS2779103 =
  lhcbBsMuMuCERN5r7hzC7e34

canonicalPenguinDatasetSourceCandidateNames :
  List PenguinDatasetSourceCandidateName
canonicalPenguinDatasetSourceCandidateNames =
  cmsHEPData135675ResultsTable
  ∷ lhcbBsMuMuCERN5r7hzC7e34
  ∷ []

datasetSourceLabel :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceLabel cmsHEPData135675ResultsTable =
  "CMS Bs0 -> mu+ mu- HEPData Results table"
datasetSourceLabel lhcbBsMuMuCERN5r7hzC7e34 =
  "LHCb Bs0 -> mu+ mu- citation authority / CERN record 5r7hz-c7e34"

datasetSourceCollaboration :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceCollaboration cmsHEPData135675ResultsTable =
  "CMS"
datasetSourceCollaboration lhcbBsMuMuCERN5r7hzC7e34 =
  "LHCb"

datasetSourceCitation :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceCitation cmsHEPData135675ResultsTable =
  "10.17182/hepdata.135675"
datasetSourceCitation lhcbBsMuMuCERN5r7hzC7e34 =
  "arXiv:2108.09283; CERN-EP-2021-133; Phys.Rev.D 104 (2021) L091102"

datasetSourceRecordIdentifier :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceRecordIdentifier cmsHEPData135675ResultsTable =
  "HEPData:ins2616304"
datasetSourceRecordIdentifier lhcbBsMuMuCERN5r7hzC7e34 =
  "repository.cern/records/5r7hz-c7e34"

datasetSourceTableIdentifier :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceTableIdentifier cmsHEPData135675ResultsTable =
  "Results"
datasetSourceTableIdentifier lhcbBsMuMuCERN5r7hzC7e34 =
  "none: HEPData deposited=false; no machine-readable table"

datasetSourceDirectTableAvailable :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceDirectTableAvailable cmsHEPData135675ResultsTable =
  true
datasetSourceDirectTableAvailable lhcbBsMuMuCERN5r7hzC7e34 =
  false

datasetSourceNoMachineReadableTable :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceNoMachineReadableTable cmsHEPData135675ResultsTable =
  false
datasetSourceNoMachineReadableTable lhcbBsMuMuCERN5r7hzC7e34 =
  true

datasetSourceArtifactAuthority :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceArtifactAuthority cmsHEPData135675ResultsTable =
  true
datasetSourceArtifactAuthority lhcbBsMuMuCERN5r7hzC7e34 =
  false

datasetSourceExactChecksumBound :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceExactChecksumBound cmsHEPData135675ResultsTable =
  true
datasetSourceExactChecksumBound lhcbBsMuMuCERN5r7hzC7e34 =
  false

data DatasetSourceDiscriminatorOutcome : Set where
  cmsChecksumAuthorityPopulatedNotThreadSelected :
    DatasetSourceDiscriminatorOutcome
  lhcbCitationAuthorityClosedNoHEPDataArtifact :
    DatasetSourceDiscriminatorOutcome
  lhcbChecksumMissingFailClosed :
    DatasetSourceDiscriminatorOutcome

datasetSourceDiscriminatorOutcome :
  PenguinDatasetSourceCandidateName →
  DatasetSourceDiscriminatorOutcome
datasetSourceDiscriminatorOutcome cmsHEPData135675ResultsTable =
  cmsChecksumAuthorityPopulatedNotThreadSelected
datasetSourceDiscriminatorOutcome lhcbBsMuMuCERN5r7hzC7e34 =
  lhcbCitationAuthorityClosedNoHEPDataArtifact

record PenguinDatasetSourceCandidate : Set where
  constructor mkPenguinDatasetSourceCandidate
  field
    candidateName :
      PenguinDatasetSourceCandidateName

    candidateLabel :
      String

    candidateLabelMatches :
      candidateLabel ≡ datasetSourceLabel candidateName

    collaboration :
      String

    collaborationMatches :
      collaboration ≡ datasetSourceCollaboration candidateName

    citation :
      String

    citationMatches :
      citation ≡ datasetSourceCitation candidateName

    recordIdentifier :
      String

    recordIdentifierMatches :
      recordIdentifier ≡ datasetSourceRecordIdentifier candidateName

    tableIdentifier :
      String

    tableIdentifierMatches :
      tableIdentifier ≡ datasetSourceTableIdentifier candidateName

    directHEPDataTableAvailable :
      Bool

    directHEPDataTableAvailableMatches :
      directHEPDataTableAvailable
      ≡
      datasetSourceDirectTableAvailable candidateName

    exactChecksumBound :
      Bool

    exactChecksumBoundMatches :
      exactChecksumBound
      ≡
      datasetSourceExactChecksumBound candidateName

    authorityKind :
      Authority.AuthorityKind

    citationAuthority :
      Authority.CitationAuthorityBoundary

    artifactAuthority :
      Bool

    artifactAuthorityMatches :
      artifactAuthority
      ≡
      datasetSourceArtifactAuthority candidateName

    hepDataDeposited :
      Bool

    hepDataDepositedMatchesDirectTable :
      hepDataDeposited
      ≡
      datasetSourceDirectTableAvailable candidateName

    noMachineReadableTable :
      Bool

    noMachineReadableTableMatches :
      noMachineReadableTable
      ≡
      datasetSourceNoMachineReadableTable candidateName

    discriminatorOutcome :
      DatasetSourceDiscriminatorOutcome

    discriminatorOutcomeMatches :
      discriminatorOutcome
      ≡
      datasetSourceDiscriminatorOutcome candidateName

open PenguinDatasetSourceCandidate public

cmsHEPData135675ResultsCandidate :
  PenguinDatasetSourceCandidate
cmsHEPData135675ResultsCandidate =
  mkPenguinDatasetSourceCandidate
    cmsHEPData135675ResultsTable
    "CMS Bs0 -> mu+ mu- HEPData Results table"
    refl
    "CMS"
    refl
    "10.17182/hepdata.135675"
    refl
    "HEPData:ins2616304"
    refl
    "Results"
    refl
    true
    refl
    true
    refl
    Authority.CitationAuthority
    (Authority.mkAuthorityBoundary
      Authority.CitationAuthority
      refl
      "10.17182/hepdata.135675"
      "CMS Bs0 -> mu+ mu- HEPData Results table"
      true
      true
      true
      ("HEPData artifact authority is available for the CMS comparison candidate"
       ∷ []))
    true
    refl
    true
    refl
    false
    refl
    cmsChecksumAuthorityPopulatedNotThreadSelected
    refl

lhcbBsMuMuCERN5r7hzC7e34CitationAuthority :
  Authority.CitationAuthorityBoundary
lhcbBsMuMuCERN5r7hzC7e34CitationAuthority =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "repository.cern/records/5r7hz-c7e34"
    "arXiv:2108.09283; CERN-EP-2021-133; Phys.Rev.D 104 (2021) L091102"
    true
    false
    false
    ( "CERN record closes the LHCb Bs->mumu source slot as CitationAuthority"
      ∷ "HEPData deposited=false"
      ∷ "artifactAuthority=false; no machine-readable table"
      ∷ "No fabricated SHA or table checksum is supplied"
      ∷ [] )

lhcbBsMuMuCERN5r7hzC7e34NoArtifactAuthority :
  Authority.CitationAuthorityNoArtifact
lhcbBsMuMuCERN5r7hzC7e34NoArtifactAuthority =
  Authority.mkCitationAuthorityNoArtifact
    lhcbBsMuMuCERN5r7hzC7e34CitationAuthority
    refl
    refl
    refl

lhcbBsMuMuCERN5r7hzC7e34Candidate :
  PenguinDatasetSourceCandidate
lhcbBsMuMuCERN5r7hzC7e34Candidate =
  mkPenguinDatasetSourceCandidate
    lhcbBsMuMuCERN5r7hzC7e34
    "LHCb Bs0 -> mu+ mu- citation authority / CERN record 5r7hz-c7e34"
    refl
    "LHCb"
    refl
    "arXiv:2108.09283; CERN-EP-2021-133; Phys.Rev.D 104 (2021) L091102"
    refl
    "repository.cern/records/5r7hz-c7e34"
    refl
    "none: HEPData deposited=false; no machine-readable table"
    refl
    false
    refl
    false
    refl
    Authority.CitationAuthority
    lhcbBsMuMuCERN5r7hzC7e34CitationAuthority
    false
    refl
    false
    refl
    true
    refl
    lhcbCitationAuthorityClosedNoHEPDataArtifact
    refl

lhcbPRD105012010CDS2779103Candidate :
  PenguinDatasetSourceCandidate
lhcbPRD105012010CDS2779103Candidate =
  lhcbBsMuMuCERN5r7hzC7e34Candidate

canonicalPenguinDatasetSourceCandidates :
  List PenguinDatasetSourceCandidate
canonicalPenguinDatasetSourceCandidates =
  cmsHEPData135675ResultsCandidate
  ∷ lhcbBsMuMuCERN5r7hzC7e34Candidate
  ∷ []

record CMSTableArtifactChecksumCandidate : Set where
  constructor mkCMSTableArtifactChecksumCandidate
  field
    localArtifactPath :
      String

    localArtifactPathIsCanonical :
      localArtifactPath
      ≡
      "/home/c/Downloads/HEPData-ins2616304-v1-Results.yaml"

    sha256 :
      String

    sha256IsSupplied :
      sha256
      ≡
      "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"

    sha256Verified :
      Bool

    sha256VerifiedIsTrue :
      sha256Verified ≡ true

    hepDataRecord :
      String

    hepDataRecordIsCanonical :
      hepDataRecord ≡ "HEPData:ins2616304:v1"

    tableDOI :
      String

    tableDOIIsCanonical :
      tableDOI ≡ "10.17182/hepdata.135675.v1/t1"

    tableIdentifier :
      String

    tableIdentifierIsCanonical :
      tableIdentifier ≡ "1435213"

    tableName :
      String

    tableNameIsResults :
      tableName ≡ "Results"

    valueSummary :
      String

    valueSummaryIsCanonical :
      valueSummary
      ≡
      "Bs->mumu branching fractions 3.83 and 3.95 in 10^-9 under two normalizations, plus B0 and lifetime entries"

    cmsChecksumAuthorityPopulated :
      Bool

    cmsChecksumAuthorityPopulatedIsTrue :
      cmsChecksumAuthorityPopulated ≡ true

    selectedThreadObservablePromoted :
      Bool

    selectedThreadObservablePromotedIsFalse :
      selectedThreadObservablePromoted ≡ false

open CMSTableArtifactChecksumCandidate public

canonicalCMSTableArtifactChecksumCandidate :
  CMSTableArtifactChecksumCandidate
canonicalCMSTableArtifactChecksumCandidate =
  mkCMSTableArtifactChecksumCandidate
    "/home/c/Downloads/HEPData-ins2616304-v1-Results.yaml"
    refl
    "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"
    refl
    true
    refl
    "HEPData:ins2616304:v1"
    refl
    "10.17182/hepdata.135675.v1/t1"
    refl
    "1435213"
    refl
    "Results"
    refl
    "Bs->mumu branching fractions 3.83 and 3.95 in 10^-9 under two normalizations, plus B0 and lifetime entries"
    refl
    true
    refl
    false
    refl

record PenguinDatasetSourceDiscriminator : Set where
  constructor mkPenguinDatasetSourceDiscriminator
  field
    candidates :
      List PenguinDatasetSourceCandidate

    candidatesAreCanonical :
      candidates ≡ canonicalPenguinDatasetSourceCandidates

    cmsCandidate :
      PenguinDatasetSourceCandidate

    cmsCandidateIsCanonical :
      cmsCandidate ≡ cmsHEPData135675ResultsCandidate

    lhcbCandidate :
      PenguinDatasetSourceCandidate

    lhcbCandidateIsCanonical :
      lhcbCandidate ≡ lhcbBsMuMuCERN5r7hzC7e34Candidate

    selectedThreadCandidate :
      PenguinDatasetSourceCandidateName

    selectedThreadCandidateIsLHCb :
      selectedThreadCandidate ≡ lhcbBsMuMuCERN5r7hzC7e34

    cmsTableArtifactChecksumCandidate :
      CMSTableArtifactChecksumCandidate

    cmsTableArtifactChecksumCandidateIsCanonical :
      cmsTableArtifactChecksumCandidate
      ≡
      canonicalCMSTableArtifactChecksumCandidate

    cmsChecksumAuthorityPopulated :
      Bool

    cmsChecksumAuthorityPopulatedIsTrue :
      cmsChecksumAuthorityPopulated ≡ true

    lhcbChecksumAuthorityPopulated :
      Bool

    lhcbChecksumAuthorityPopulatedIsFalse :
      lhcbChecksumAuthorityPopulated ≡ false

    cmsCandidateOutcome :
      DatasetSourceDiscriminatorOutcome

    cmsCandidateOutcomeIsChecksumPopulatedNotThreadSelected :
      cmsCandidateOutcome ≡ cmsChecksumAuthorityPopulatedNotThreadSelected

    lhcbCandidateOutcome :
      DatasetSourceDiscriminatorOutcome

    lhcbCandidateOutcomeIsCitationAuthorityClosed :
      lhcbCandidateOutcome ≡ lhcbCitationAuthorityClosedNoHEPDataArtifact

    exactChecksumAcceptedHere :
      Bool

    exactChecksumAcceptedHereIsFalse :
      exactChecksumAcceptedHere ≡ false

    currentDiagnostic :
      String

    currentDiagnosticIsCanonical :
      currentDiagnostic
      ≡
      "CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results is checksum-populated; the thread-selected LHCb CERN record repository.cern/records/5r7hz-c7e34 is closed only as CitationAuthority with HEPData deposited=false, artifactAuthority=false, and no machine-readable table"

open PenguinDatasetSourceDiscriminator public

canonicalPenguinDatasetSourceDiscriminator :
  PenguinDatasetSourceDiscriminator
canonicalPenguinDatasetSourceDiscriminator =
  mkPenguinDatasetSourceDiscriminator
    canonicalPenguinDatasetSourceCandidates
    refl
    cmsHEPData135675ResultsCandidate
    refl
    lhcbBsMuMuCERN5r7hzC7e34Candidate
    refl
    lhcbBsMuMuCERN5r7hzC7e34
    refl
    canonicalCMSTableArtifactChecksumCandidate
    refl
    true
    refl
    false
    refl
    cmsChecksumAuthorityPopulatedNotThreadSelected
    refl
    lhcbCitationAuthorityClosedNoHEPDataArtifact
    refl
    false
    refl
    "CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results is checksum-populated; the thread-selected LHCb CERN record repository.cern/records/5r7hz-c7e34 is closed only as CitationAuthority with HEPData deposited=false, artifactAuthority=false, and no machine-readable table"
    refl

data HEPDataTableChecksumMissingAuthority : Set where
  hepDataDepositedFalse :
    HEPDataTableChecksumMissingAuthority
  noHEPDataValueTable :
    HEPDataTableChecksumMissingAuthority
  noHEPDataPayloadFileName :
    HEPDataTableChecksumMissingAuthority
  noHEPDataPayloadSHA256 :
    HEPDataTableChecksumMissingAuthority

canonicalHEPDataTableChecksumMissingAuthorities :
  List HEPDataTableChecksumMissingAuthority
canonicalHEPDataTableChecksumMissingAuthorities =
  hepDataDepositedFalse
  ∷ noHEPDataValueTable
  ∷ noHEPDataPayloadFileName
  ∷ noHEPDataPayloadSHA256
  ∷ []

record HEPDataTableChecksumSlot : Set where
  constructor mkHEPDataTableChecksumSlot
  field
    recordIdentifierSlot :
      String

    recordIdentifierSlotIsRequired :
      recordIdentifierSlot
      ≡
      "citation authority: repository.cern/records/5r7hz-c7e34"

    valueTableIdentifierSlot :
      String

    valueTableIdentifierSlotIsRequired :
      valueTableIdentifierSlot
      ≡
      "none: HEPData deposited=false; no machine-readable value table"

    payloadFileNameSlot :
      String

    payloadFileNameSlotIsRequired :
      payloadFileNameSlot
      ≡
      "none: no HEPData payload file exists for this citation authority slot"

    payloadSHA256Slot :
      String

    payloadSHA256SlotIsRequired :
      payloadSHA256Slot
      ≡
      "none: no fabricated SHA; artifactAuthority=false"

    missingAuthorities :
      List HEPDataTableChecksumMissingAuthority

    missingAuthoritiesAreCanonical :
      missingAuthorities
      ≡
      canonicalHEPDataTableChecksumMissingAuthorities

open HEPDataTableChecksumSlot public

canonicalLHCbBs0MuMuHEPDataTableChecksumSlot :
  HEPDataTableChecksumSlot
canonicalLHCbBs0MuMuHEPDataTableChecksumSlot =
  mkHEPDataTableChecksumSlot
    "citation authority: repository.cern/records/5r7hz-c7e34"
    refl
    "none: HEPData deposited=false; no machine-readable value table"
    refl
    "none: no HEPData payload file exists for this citation authority slot"
    refl
    "none: no fabricated SHA; artifactAuthority=false"
    refl
    canonicalHEPDataTableChecksumMissingAuthorities
    refl

record HEPDataTableBinding : Set where
  constructor mkHEPDataTableBinding
  field
    bindingFields :
      List HEPDataTableBindingField

    bindingFieldsAreCanonical :
      bindingFields ≡ canonicalHEPDataTableBindingFields

    sourceCollaboration :
      String

    sourceCollaborationIsLHCb :
      sourceCollaboration ≡ "LHCb"

    sourceCDSRecordIdentifier :
      String

    sourceCDSRecordIdentifierIsCanonical :
      sourceCDSRecordIdentifier ≡ "repository.cern/records/5r7hz-c7e34"

    sourceJournalDOI :
      String

    sourceJournalDOIIsCanonical :
      sourceJournalDOI ≡ "Phys.Rev.D 104 (2021) L091102"

    citationAuthority :
      Authority.CitationAuthorityBoundary

    citationAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    hepDataDeposited :
      Bool

    hepDataDepositedIsFalse :
      hepDataDeposited ≡ false

    artifactAuthority :
      Bool

    artifactAuthorityIsFalse :
      artifactAuthority ≡ false

    machineReadableTablePresent :
      Bool

    machineReadableTablePresentIsFalse :
      machineReadableTablePresent ≡ false

    hepDataRecordIdentifierObligation :
      String

    hepDataRecordIdentifierObligationIsCanonical :
      hepDataRecordIdentifierObligation
      ≡
      "closed by CitationAuthority repository.cern/records/5r7hz-c7e34; HEPData deposited=false"

    hepDataTableIdentifierObligation :
      String

    hepDataTableIdentifierObligationIsCanonical :
      hepDataTableIdentifierObligation
      ≡
      "none: no machine-readable HEPData table is deposited for this citation slot"

    hepDataPayloadFileObligation :
      String

    hepDataPayloadFileObligationIsCanonical :
      hepDataPayloadFileObligation
      ≡
      "none: no HEPData payload file is available from the citation authority"

    hepDataPayloadChecksumObligation :
      String

    hepDataPayloadChecksumObligationIsCanonical :
      hepDataPayloadChecksumObligation
      ≡
      "none: no fabricated SHA; artifactAuthority=false"

    checksumAuthorityStatus :
      HEPDataChecksumAuthorityStatus

    checksumAuthorityStatusIsFailClosed :
      checksumAuthorityStatus ≡ checksumAuthorityMissingFailClosed

    checksumSlot :
      HEPDataTableChecksumSlot

    checksumSlotIsCanonical :
      checksumSlot
      ≡
      canonicalLHCbBs0MuMuHEPDataTableChecksumSlot

    exactChecksumVerifiedHere :
      Bool

    exactChecksumVerifiedHereIsFalse :
      exactChecksumVerifiedHere ≡ false

    acceptedHEPDataTableAuthorityHere :
      Bool

    acceptedHEPDataTableAuthorityHereIsFalse :
      acceptedHEPDataTableAuthorityHere ≡ false

open HEPDataTableBinding public

canonicalLHCbBs0MuMuHEPDataTableBinding :
  HEPDataTableBinding
canonicalLHCbBs0MuMuHEPDataTableBinding =
  mkHEPDataTableBinding
    canonicalHEPDataTableBindingFields
    refl
    "LHCb"
    refl
    "repository.cern/records/5r7hz-c7e34"
    refl
    "Phys.Rev.D 104 (2021) L091102"
    refl
    lhcbBsMuMuCERN5r7hzC7e34CitationAuthority
    lhcbBsMuMuCERN5r7hzC7e34NoArtifactAuthority
    false
    refl
    false
    refl
    false
    refl
    "closed by CitationAuthority repository.cern/records/5r7hz-c7e34; HEPData deposited=false"
    refl
    "none: no machine-readable HEPData table is deposited for this citation slot"
    refl
    "none: no HEPData payload file is available from the citation authority"
    refl
    "none: no fabricated SHA; artifactAuthority=false"
    refl
    checksumAuthorityMissingFailClosed
    refl
    canonicalLHCbBs0MuMuHEPDataTableChecksumSlot
    refl
    false
    refl
    false
    refl

data ConcretePenguinObservableName : Set where
  lhcbBs0ToMuMuBranchingFraction :
    ConcretePenguinObservableName

observableNameLabel :
  ConcretePenguinObservableName →
  String
observableNameLabel lhcbBs0ToMuMuBranchingFraction =
  "LHCb B(Bs0 -> mu+ mu-) branching fraction"

data BranchingRatioPayloadField : Set where
  measuredCentralValue :
    BranchingRatioPayloadField
  measuredStatisticalUncertainty :
    BranchingRatioPayloadField
  measuredSystematicUncertainty :
    BranchingRatioPayloadField
  measuredScale :
    BranchingRatioPayloadField

canonicalBranchingRatioPayloadFields :
  List BranchingRatioPayloadField
canonicalBranchingRatioPayloadFields =
  measuredCentralValue
  ∷ measuredStatisticalUncertainty
  ∷ measuredSystematicUncertainty
  ∷ measuredScale
  ∷ []

record DatasetAuthorityBinding : Set where
  constructor mkDatasetAuthorityBinding
  field
    authorityNamespaces :
      List DatasetAuthorityNamespace

    authorityNamespacesAreCanonical :
      authorityNamespaces ≡ canonicalDatasetAuthorityNamespaces

    collaboration :
      String

    collaborationIsLHCb :
      collaboration ≡ "LHCb"

    cernCDSRecordIdentifier :
      String

    cernCDSRecordIdentifierIsCanonical :
      cernCDSRecordIdentifier ≡ "repository.cern/records/5r7hz-c7e34"

    journalDOI :
      String

    journalDOIIsCanonical :
      journalDOI ≡ "Phys.Rev.D 104 (2021) L091102"

    citationAuthority :
      Authority.CitationAuthorityBoundary

    citationAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    citationAuthorityAccepted :
      Bool

    citationAuthorityAcceptedIsTrue :
      citationAuthorityAccepted ≡ true

    artifactAuthority :
      Bool

    artifactAuthorityIsFalse :
      artifactAuthority ≡ false

    hepDataDeposited :
      Bool

    hepDataDepositedIsFalse :
      hepDataDeposited ≡ false

    hepDataRecordObligation :
      String

    tableBindingObligation :
      String

    checksumObligation :
      String

    hepDataTableBinding :
      HEPDataTableBinding

    hepDataTableBindingIsCanonical :
      hepDataTableBinding ≡ canonicalLHCbBs0MuMuHEPDataTableBinding

    acceptedDatasetAuthorityHere :
      Bool

    acceptedDatasetAuthorityHereIsFalse :
      acceptedDatasetAuthorityHere ≡ false

open DatasetAuthorityBinding public

canonicalLHCbBs0MuMuDatasetAuthorityBinding :
  DatasetAuthorityBinding
canonicalLHCbBs0MuMuDatasetAuthorityBinding =
  mkDatasetAuthorityBinding
    canonicalDatasetAuthorityNamespaces
    refl
    "LHCb"
    refl
    "repository.cern/records/5r7hz-c7e34"
    refl
    "Phys.Rev.D 104 (2021) L091102"
    refl
    lhcbBsMuMuCERN5r7hzC7e34CitationAuthority
    lhcbBsMuMuCERN5r7hzC7e34NoArtifactAuthority
    true
    refl
    false
    refl
    false
    refl
    "CitationAuthority closes source identification via repository.cern/records/5r7hz-c7e34"
    "artifactAuthority=false; no HEPData machine-readable table is available"
    "no fabricated SHA or table checksum is supplied for the LHCb citation slot"
    canonicalLHCbBs0MuMuHEPDataTableBinding
    refl
    false
    refl

record MeasuredBranchingRatioPayload : Set where
  constructor mkMeasuredBranchingRatioPayload
  field
    observableName :
      ConcretePenguinObservableName

    observableNameIsSelected :
      observableName ≡ lhcbBs0ToMuMuBranchingFraction

    observableNameText :
      String

    observableNameTextMatches :
      observableNameText ≡ observableNameLabel observableName

    descriptor :
      PenguinObservableDescriptor

    descriptorIsBranchingRatio :
      descriptor ≡ branchingRatioDescriptor

    unit :
      ObservableUnitConvention

    unitIsDimensionlessRatio :
      unit ≡ dimensionlessRatio

    payloadFields :
      List BranchingRatioPayloadField

    payloadFieldsAreCanonical :
      payloadFields ≡ canonicalBranchingRatioPayloadFields

    centralValue :
      String

    centralValueIsCanonical :
      centralValue ≡ "3.09"

    scale :
      String

    scaleIsCanonical :
      scale ≡ "1e-9"

    statisticalUncertaintyPlus :
      String

    statisticalUncertaintyPlusIsCanonical :
      statisticalUncertaintyPlus ≡ "+0.46"

    statisticalUncertaintyMinus :
      String

    statisticalUncertaintyMinusIsCanonical :
      statisticalUncertaintyMinus ≡ "-0.43"

    systematicUncertaintyPlus :
      String

    systematicUncertaintyPlusIsCanonical :
      systematicUncertaintyPlus ≡ "+0.15"

    systematicUncertaintyMinus :
      String

    systematicUncertaintyMinusIsCanonical :
      systematicUncertaintyMinus ≡ "-0.11"

    sourceBinding :
      DatasetAuthorityBinding

    sourceBindingIsCanonical :
      sourceBinding ≡ canonicalLHCbBs0MuMuDatasetAuthorityBinding

    acceptedEmpiricalPromotionFromPayload :
      Bool

    acceptedEmpiricalPromotionFromPayloadIsFalse :
      acceptedEmpiricalPromotionFromPayload ≡ false

open MeasuredBranchingRatioPayload public

canonicalLHCbBs0MuMuMeasuredBranchingRatioPayload :
  MeasuredBranchingRatioPayload
canonicalLHCbBs0MuMuMeasuredBranchingRatioPayload =
  mkMeasuredBranchingRatioPayload
    lhcbBs0ToMuMuBranchingFraction
    refl
    "LHCb B(Bs0 -> mu+ mu-) branching fraction"
    refl
    branchingRatioDescriptor
    refl
    dimensionlessRatio
    refl
    canonicalBranchingRatioPayloadFields
    refl
    "3.09"
    refl
    "1e-9"
    refl
    "+0.46"
    refl
    "-0.43"
    refl
    "+0.15"
    refl
    "-0.11"
    refl
    canonicalLHCbBs0MuMuDatasetAuthorityBinding
    refl
    false
    refl

data SMBaselineNumericAuthorityRequestField : Set where
  smCentralValueAuthority :
    SMBaselineNumericAuthorityRequestField
  smTheoryUncertaintyAuthority :
    SMBaselineNumericAuthorityRequestField
  smObservableDefinitionAuthority :
    SMBaselineNumericAuthorityRequestField
  smCitationAuthority :
    SMBaselineNumericAuthorityRequestField
  smChecksumOrDigestAuthority :
    SMBaselineNumericAuthorityRequestField
  smNoManualFitAttestation :
    SMBaselineNumericAuthorityRequestField

canonicalSMBaselineNumericAuthorityRequestFields :
  List SMBaselineNumericAuthorityRequestField
canonicalSMBaselineNumericAuthorityRequestFields =
  smCentralValueAuthority
  ∷ smTheoryUncertaintyAuthority
  ∷ smObservableDefinitionAuthority
  ∷ smCitationAuthority
  ∷ smChecksumOrDigestAuthority
  ∷ smNoManualFitAttestation
  ∷ []

record SMBaselineNumericAuthorityRequest : Set where
  constructor mkSMBaselineNumericAuthorityRequest
  field
    targetObservableName :
      ConcretePenguinObservableName

    targetObservableNameIsSelected :
      targetObservableName ≡ lhcbBs0ToMuMuBranchingFraction

    requestedFields :
      List SMBaselineNumericAuthorityRequestField

    requestedFieldsAreCanonical :
      requestedFields ≡ canonicalSMBaselineNumericAuthorityRequestFields

    requestedFieldLabels :
      List String

    requestTargetProcess :
      String

    requestTargetProcessIsCanonical :
      requestTargetProcess ≡ "b -> s mu+ mu- / Bs0 -> mu+ mu- branching fraction"

    requestedSMCentralValue :
      String

    requestedSMUncertainty :
      String

    requestedSMSourceCitation :
      String

    acceptedSMBaselineNumericAuthorityHere :
      Bool

    acceptedSMBaselineNumericAuthorityHereIsFalse :
      acceptedSMBaselineNumericAuthorityHere ≡ false

    empiricalComparisonConstructedHere :
      Bool

    empiricalComparisonConstructedHereIsFalse :
      empiricalComparisonConstructedHere ≡ false

open SMBaselineNumericAuthorityRequest public

canonicalSMBaselineNumericAuthorityRequest :
  SMBaselineNumericAuthorityRequest
canonicalSMBaselineNumericAuthorityRequest =
  mkSMBaselineNumericAuthorityRequest
    lhcbBs0ToMuMuBranchingFraction
    refl
    canonicalSMBaselineNumericAuthorityRequestFields
    refl
    ( "sm_central_value"
      ∷ "sm_theory_uncertainty"
      ∷ "sm_observable_definition"
      ∷ "sm_source_citation"
      ∷ "sm_checksum_or_digest"
      ∷ "no_manual_fit_attestation"
      ∷ [] )
    "b -> s mu+ mu- / Bs0 -> mu+ mu- branching fraction"
    refl
    "requested from accepted Standard-Model baseline authority"
    "requested from accepted Standard-Model baseline authority"
    "requested DOI/table/checksum-bound Standard-Model baseline source"
    false
    refl
    false
    refl

data PenguinObservableNonPromotionBoundary : Set where
  noAcceptedExternalEmpiricalAuthorityHere :
    PenguinObservableNonPromotionBoundary
  noNumericalFitOrPullComputationHere :
    PenguinObservableNonPromotionBoundary
  noProjectionRunnerOrDigestHere :
    PenguinObservableNonPromotionBoundary
  noStandardModelAmplitudeReceiptHere :
    PenguinObservableNonPromotionBoundary
  noHadronicUncertaintyModelReceiptHere :
    PenguinObservableNonPromotionBoundary
  noWilsonCoefficientExtractionHere :
    PenguinObservableNonPromotionBoundary
  noNonSMDiscoveryOrPromotionHere :
    PenguinObservableNonPromotionBoundary

canonicalNonPromotionBoundaries :
  List PenguinObservableNonPromotionBoundary
canonicalNonPromotionBoundaries =
  noAcceptedExternalEmpiricalAuthorityHere
  ∷ noNumericalFitOrPullComputationHere
  ∷ noProjectionRunnerOrDigestHere
  ∷ noStandardModelAmplitudeReceiptHere
  ∷ noHadronicUncertaintyModelReceiptHere
  ∷ noWilsonCoefficientExtractionHere
  ∷ noNonSMDiscoveryOrPromotionHere
  ∷ []

data PenguinObservablePromotionToken : Set where

penguinObservablePromotionImpossibleHere :
  PenguinObservablePromotionToken →
  ⊥
penguinObservablePromotionImpossibleHere ()

record PenguinDecayObservableContract : Set where
  field
    status :
      PenguinObservableContractStatus

    projectionDefectReceipt :
      R.PenguinDecayProjectionDefectReceipt

    selectedDecay :
      R.RarePenguinDecay

    selectedDecayIsCanonical :
      selectedDecay ≡ R.bToSLeptonPair

    selectedLeptonPair :
      LeptonPairChannel

    observableKinds :
      List PenguinObservableKind

    observableKindsAreCanonical :
      observableKinds ≡ canonicalPenguinObservableKinds

    observableDescriptors :
      List PenguinObservableDescriptor

    observableDescriptorsAreCanonical :
      observableDescriptors ≡ canonicalPenguinObservableDescriptors

    descriptorLookup :
      PenguinObservableKind →
      PenguinObservableDescriptor

    descriptorLookupMatchesKind :
      (kind : PenguinObservableKind) →
      observableKind (descriptorLookup kind) ≡ kind

    witnessForDescriptor :
      PenguinObservableDescriptor →
      R.IndirectWitness

    witnessForDescriptorIsIndirect :
      (descriptor : PenguinObservableDescriptor) →
      R.extractionMode (witnessForDescriptor descriptor)
      ≡
      R.indirectProjectionDefectExtraction

    witnessForDescriptorReturnsSMProjection :
      (descriptor : PenguinObservableDescriptor) →
      R.projectedAmplitude (witnessForDescriptor descriptor)
      ≡
      R.standardModelSurface

    witnessForDescriptorReturnsResidualDefect :
      (descriptor : PenguinObservableDescriptor) →
      R.extractedDefect (witnessForDescriptor descriptor)
      ≡
      R.residualDefectSurface

    authorityRequired :
      Bool

    authorityRequiredIsTrue :
      authorityRequired ≡ true

    acceptedAuthorityReceiptPresent :
      Bool

    acceptedAuthorityReceiptPresentIsFalse :
      acceptedAuthorityReceiptPresent ≡ false

    authorityRequiredFields :
      List PenguinObservableAuthorityField

    authorityRequiredFieldsAreCanonical :
      authorityRequiredFields ≡ canonicalAuthorityRequiredFields

    authorityRequiredFieldNames :
      List String

    selectedConcreteObservableName :
      ConcretePenguinObservableName

    selectedConcreteObservableNameIsLHCbBs0MuMu :
      selectedConcreteObservableName ≡ lhcbBs0ToMuMuBranchingFraction

    selectedConcreteObservableNameText :
      String

    selectedConcreteObservableNameTextMatches :
      selectedConcreteObservableNameText
      ≡
      observableNameLabel selectedConcreteObservableName

    datasetAuthorityBinding :
      DatasetAuthorityBinding

    datasetAuthorityBindingIsCanonical :
      datasetAuthorityBinding
      ≡
      canonicalLHCbBs0MuMuDatasetAuthorityBinding

    datasetSourceDiscriminator :
      PenguinDatasetSourceDiscriminator

    datasetSourceDiscriminatorIsCanonical :
      datasetSourceDiscriminator
      ≡
      canonicalPenguinDatasetSourceDiscriminator

    hepDataTableBinding :
      HEPDataTableBinding

    hepDataTableBindingIsCanonical :
      hepDataTableBinding
      ≡
      canonicalLHCbBs0MuMuHEPDataTableBinding

    measuredBranchingRatioPayload :
      MeasuredBranchingRatioPayload

    measuredBranchingRatioPayloadIsCanonical :
      measuredBranchingRatioPayload
      ≡
      canonicalLHCbBs0MuMuMeasuredBranchingRatioPayload

    smBaselineNumericAuthorityRequest :
      SMBaselineNumericAuthorityRequest

    smBaselineNumericAuthorityRequestIsCanonical :
      smBaselineNumericAuthorityRequest
      ≡
      canonicalSMBaselineNumericAuthorityRequest

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    nonSMPromotionConstructedHere :
      Bool

    nonSMPromotionConstructedHereIsFalse :
      nonSMPromotionConstructedHere ≡ false

    nonPromotionBoundaries :
      List PenguinObservableNonPromotionBoundary

    nonPromotionBoundariesAreCanonical :
      nonPromotionBoundaries ≡ canonicalNonPromotionBoundaries

    promotionTokenBlocked :
      PenguinObservablePromotionToken →
      ⊥

open PenguinDecayObservableContract public

descriptorLookupMatchesKindCanonical :
  (kind : PenguinObservableKind) →
  observableKind (descriptorForKind kind) ≡ kind
descriptorLookupMatchesKindCanonical branchingRatio =
  refl
descriptorLookupMatchesKindCanonical angularCoefficient =
  refl
descriptorLookupMatchesKindCanonical cpAsymmetry =
  refl

canonicalPenguinDecayObservableContract :
  PenguinDecayObservableContract
canonicalPenguinDecayObservableContract =
  record
    { status =
        concreteBToSMuonPairProjectionDefectObservableNonPromoting
    ; projectionDefectReceipt =
        canonicalPenguinReceipt
    ; selectedDecay =
        selectedCanonicalTarget
    ; selectedDecayIsCanonical =
        refl
    ; selectedLeptonPair =
        muonPair
    ; observableKinds =
        canonicalPenguinObservableKinds
    ; observableKindsAreCanonical =
        refl
    ; observableDescriptors =
        canonicalPenguinObservableDescriptors
    ; observableDescriptorsAreCanonical =
        refl
    ; descriptorLookup =
        descriptorForKind
    ; descriptorLookupMatchesKind =
        descriptorLookupMatchesKindCanonical
    ; witnessForDescriptor =
        descriptorWitness
    ; witnessForDescriptorIsIndirect =
        descriptorWitnessIsIndirect
    ; witnessForDescriptorReturnsSMProjection =
        descriptorWitnessReturnsSMProjection
    ; witnessForDescriptorReturnsResidualDefect =
        descriptorWitnessReturnsResidualDefect
    ; authorityRequired =
        true
    ; authorityRequiredIsTrue =
        refl
    ; acceptedAuthorityReceiptPresent =
        false
    ; acceptedAuthorityReceiptPresentIsFalse =
        refl
    ; authorityRequiredFields =
        canonicalAuthorityRequiredFields
    ; authorityRequiredFieldsAreCanonical =
        refl
    ; authorityRequiredFieldNames =
        canonicalAuthorityRequiredFieldNames
    ; selectedConcreteObservableName =
        lhcbBs0ToMuMuBranchingFraction
    ; selectedConcreteObservableNameIsLHCbBs0MuMu =
        refl
    ; selectedConcreteObservableNameText =
        "LHCb B(Bs0 -> mu+ mu-) branching fraction"
    ; selectedConcreteObservableNameTextMatches =
        refl
    ; datasetAuthorityBinding =
        canonicalLHCbBs0MuMuDatasetAuthorityBinding
    ; datasetAuthorityBindingIsCanonical =
        refl
    ; datasetSourceDiscriminator =
        canonicalPenguinDatasetSourceDiscriminator
    ; datasetSourceDiscriminatorIsCanonical =
        refl
    ; hepDataTableBinding =
        canonicalLHCbBs0MuMuHEPDataTableBinding
    ; hepDataTableBindingIsCanonical =
        refl
    ; measuredBranchingRatioPayload =
        canonicalLHCbBs0MuMuMeasuredBranchingRatioPayload
    ; measuredBranchingRatioPayloadIsCanonical =
        refl
    ; smBaselineNumericAuthorityRequest =
        canonicalSMBaselineNumericAuthorityRequest
    ; smBaselineNumericAuthorityRequestIsCanonical =
        refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; nonSMPromotionConstructedHere =
        false
    ; nonSMPromotionConstructedHereIsFalse =
        refl
    ; nonPromotionBoundaries =
        canonicalNonPromotionBoundaries
    ; nonPromotionBoundariesAreCanonical =
        refl
    ; promotionTokenBlocked =
        penguinObservablePromotionImpossibleHere
    }

canonicalContractSelectedTarget :
  R.RarePenguinDecay
canonicalContractSelectedTarget =
  PenguinDecayObservableContract.selectedDecay
    canonicalPenguinDecayObservableContract

canonicalContractSelectedTargetIsBToSLeptonPair :
  canonicalContractSelectedTarget ≡ R.bToSLeptonPair
canonicalContractSelectedTargetIsBToSLeptonPair =
  refl

canonicalContractAuthorityRequired :
  PenguinDecayObservableContract.authorityRequired
    canonicalPenguinDecayObservableContract
  ≡
  true
canonicalContractAuthorityRequired =
  refl

canonicalContractIsNonPromoting :
  PenguinDecayObservableContract.promoted
    canonicalPenguinDecayObservableContract
  ≡
  false
canonicalContractIsNonPromoting =
  refl
