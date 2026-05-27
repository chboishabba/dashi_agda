module DASHI.Physics.Closure.PenguinDecayObservableContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as R

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
  lhcbPRD105012010CDS2779103 :
    PenguinDatasetSourceCandidateName

canonicalPenguinDatasetSourceCandidateNames :
  List PenguinDatasetSourceCandidateName
canonicalPenguinDatasetSourceCandidateNames =
  cmsHEPData135675ResultsTable
  ∷ lhcbPRD105012010CDS2779103
  ∷ []

datasetSourceLabel :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceLabel cmsHEPData135675ResultsTable =
  "CMS Bs0 -> mu+ mu- HEPData Results table"
datasetSourceLabel lhcbPRD105012010CDS2779103 =
  "LHCb Bs0 -> mu+ mu- PRD 105.012010 / CERN-CDS 2779103"

datasetSourceCollaboration :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceCollaboration cmsHEPData135675ResultsTable =
  "CMS"
datasetSourceCollaboration lhcbPRD105012010CDS2779103 =
  "LHCb"

datasetSourceCitation :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceCitation cmsHEPData135675ResultsTable =
  "10.17182/hepdata.135675"
datasetSourceCitation lhcbPRD105012010CDS2779103 =
  "10.1103/PhysRevD.105.012010; CERN-CDS:2779103"

datasetSourceRecordIdentifier :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceRecordIdentifier cmsHEPData135675ResultsTable =
  "HEPData:ins2616304"
datasetSourceRecordIdentifier lhcbPRD105012010CDS2779103 =
  "CERN-CDS:2779103"

datasetSourceTableIdentifier :
  PenguinDatasetSourceCandidateName →
  String
datasetSourceTableIdentifier cmsHEPData135675ResultsTable =
  "Results"
datasetSourceTableIdentifier lhcbPRD105012010CDS2779103 =
  "required: exact LHCb HEPData table identifier or authoritative no-HEPData-table attestation"

datasetSourceDirectTableAvailable :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceDirectTableAvailable cmsHEPData135675ResultsTable =
  true
datasetSourceDirectTableAvailable lhcbPRD105012010CDS2779103 =
  false

datasetSourceExactChecksumBound :
  PenguinDatasetSourceCandidateName →
  Bool
datasetSourceExactChecksumBound cmsHEPData135675ResultsTable =
  true
datasetSourceExactChecksumBound lhcbPRD105012010CDS2779103 =
  false

data DatasetSourceDiscriminatorOutcome : Set where
  cmsChecksumAuthorityPopulatedNotThreadSelected :
    DatasetSourceDiscriminatorOutcome
  lhcbChecksumMissingFailClosed :
    DatasetSourceDiscriminatorOutcome

datasetSourceDiscriminatorOutcome :
  PenguinDatasetSourceCandidateName →
  DatasetSourceDiscriminatorOutcome
datasetSourceDiscriminatorOutcome cmsHEPData135675ResultsTable =
  cmsChecksumAuthorityPopulatedNotThreadSelected
datasetSourceDiscriminatorOutcome lhcbPRD105012010CDS2779103 =
  lhcbChecksumMissingFailClosed

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
    cmsChecksumAuthorityPopulatedNotThreadSelected
    refl

lhcbPRD105012010CDS2779103Candidate :
  PenguinDatasetSourceCandidate
lhcbPRD105012010CDS2779103Candidate =
  mkPenguinDatasetSourceCandidate
    lhcbPRD105012010CDS2779103
    "LHCb Bs0 -> mu+ mu- PRD 105.012010 / CERN-CDS 2779103"
    refl
    "LHCb"
    refl
    "10.1103/PhysRevD.105.012010; CERN-CDS:2779103"
    refl
    "CERN-CDS:2779103"
    refl
    "required: exact LHCb HEPData table identifier or authoritative no-HEPData-table attestation"
    refl
    false
    refl
    false
    refl
    lhcbChecksumMissingFailClosed
    refl

canonicalPenguinDatasetSourceCandidates :
  List PenguinDatasetSourceCandidate
canonicalPenguinDatasetSourceCandidates =
  cmsHEPData135675ResultsCandidate
  ∷ lhcbPRD105012010CDS2779103Candidate
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
      lhcbCandidate ≡ lhcbPRD105012010CDS2779103Candidate

    selectedThreadCandidate :
      PenguinDatasetSourceCandidateName

    selectedThreadCandidateIsLHCb :
      selectedThreadCandidate ≡ lhcbPRD105012010CDS2779103

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

    lhcbCandidateOutcomeIsChecksumMissingFailClosed :
      lhcbCandidateOutcome ≡ lhcbChecksumMissingFailClosed

    exactChecksumAcceptedHere :
      Bool

    exactChecksumAcceptedHereIsFalse :
      exactChecksumAcceptedHere ≡ false

    currentDiagnostic :
      String

    currentDiagnosticIsCanonical :
      currentDiagnostic
      ≡
      "CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results is checksum-populated by sha256 08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb; the thread-selected LHCb DOI 10.1103/PhysRevD.105.012010 / CDS 2779103 checksum is not bound, so the selected dataset lane fails closed"

open PenguinDatasetSourceDiscriminator public

canonicalPenguinDatasetSourceDiscriminator :
  PenguinDatasetSourceDiscriminator
canonicalPenguinDatasetSourceDiscriminator =
  mkPenguinDatasetSourceDiscriminator
    canonicalPenguinDatasetSourceCandidates
    refl
    cmsHEPData135675ResultsCandidate
    refl
    lhcbPRD105012010CDS2779103Candidate
    refl
    lhcbPRD105012010CDS2779103
    refl
    canonicalCMSTableArtifactChecksumCandidate
    refl
    true
    refl
    false
    refl
    cmsChecksumAuthorityPopulatedNotThreadSelected
    refl
    lhcbChecksumMissingFailClosed
    refl
    false
    refl
    "CMS HEPData DOI 10.17182/hepdata.135675.v1/t1 record ins2616304 v1 table 1435213 Results is checksum-populated by sha256 08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb; the thread-selected LHCb DOI 10.1103/PhysRevD.105.012010 / CDS 2779103 checksum is not bound, so the selected dataset lane fails closed"
    refl

data HEPDataTableChecksumMissingAuthority : Set where
  missingHEPDataPublicationRecordIdentifier :
    HEPDataTableChecksumMissingAuthority
  missingHEPDataValueTableIdentifier :
    HEPDataTableChecksumMissingAuthority
  missingHEPDataPayloadFileName :
    HEPDataTableChecksumMissingAuthority
  missingHEPDataPayloadSHA256 :
    HEPDataTableChecksumMissingAuthority

canonicalHEPDataTableChecksumMissingAuthorities :
  List HEPDataTableChecksumMissingAuthority
canonicalHEPDataTableChecksumMissingAuthorities =
  missingHEPDataPublicationRecordIdentifier
  ∷ missingHEPDataValueTableIdentifier
  ∷ missingHEPDataPayloadFileName
  ∷ missingHEPDataPayloadSHA256
  ∷ []

record HEPDataTableChecksumSlot : Set where
  constructor mkHEPDataTableChecksumSlot
  field
    recordIdentifierSlot :
      String

    recordIdentifierSlotIsRequired :
      recordIdentifierSlot
      ≡
      "required: HEPData publication record identifier for DOI 10.1103/PhysRevD.105.012010"

    valueTableIdentifierSlot :
      String

    valueTableIdentifierSlotIsRequired :
      valueTableIdentifierSlot
      ≡
      "required: exact HEPData value table identifier for B(Bs0 -> mu+ mu-)"

    payloadFileNameSlot :
      String

    payloadFileNameSlotIsRequired :
      payloadFileNameSlot
      ≡
      "required: exact HEPData payload file name for selected value table"

    payloadSHA256Slot :
      String

    payloadSHA256SlotIsRequired :
      payloadSHA256Slot
      ≡
      "required: sha256 digest of exact selected HEPData payload file"

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
    "required: HEPData publication record identifier for DOI 10.1103/PhysRevD.105.012010"
    refl
    "required: exact HEPData value table identifier for B(Bs0 -> mu+ mu-)"
    refl
    "required: exact HEPData payload file name for selected value table"
    refl
    "required: sha256 digest of exact selected HEPData payload file"
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
      sourceCDSRecordIdentifier ≡ "CERN-CDS:2779103"

    sourceJournalDOI :
      String

    sourceJournalDOIIsCanonical :
      sourceJournalDOI ≡ "10.1103/PhysRevD.105.012010"

    hepDataRecordIdentifierObligation :
      String

    hepDataRecordIdentifierObligationIsCanonical :
      hepDataRecordIdentifierObligation
      ≡
      "bind the HEPData publication record identifier for DOI 10.1103/PhysRevD.105.012010, or bind an authoritative no-HEPData-record attestation"

    hepDataTableIdentifierObligation :
      String

    hepDataTableIdentifierObligationIsCanonical :
      hepDataTableIdentifierObligation
      ≡
      "bind the exact HEPData table identifier containing B(Bs0 -> mu+ mu-)"

    hepDataPayloadFileObligation :
      String

    hepDataPayloadFileObligationIsCanonical :
      hepDataPayloadFileObligation
      ≡
      "bind the exact HEPData payload file name for the selected branching-fraction table"

    hepDataPayloadChecksumObligation :
      String

    hepDataPayloadChecksumObligationIsCanonical :
      hepDataPayloadChecksumObligation
      ≡
      "bind an authority-supplied checksum or digest for the exact selected HEPData payload file"

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
    "CERN-CDS:2779103"
    refl
    "10.1103/PhysRevD.105.012010"
    refl
    "bind the HEPData publication record identifier for DOI 10.1103/PhysRevD.105.012010, or bind an authoritative no-HEPData-record attestation"
    refl
    "bind the exact HEPData table identifier containing B(Bs0 -> mu+ mu-)"
    refl
    "bind the exact HEPData payload file name for the selected branching-fraction table"
    refl
    "bind an authority-supplied checksum or digest for the exact selected HEPData payload file"
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
      cernCDSRecordIdentifier ≡ "CERN-CDS:2779103"

    journalDOI :
      String

    journalDOIIsCanonical :
      journalDOI ≡ "10.1103/PhysRevD.105.012010"

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
    "CERN-CDS:2779103"
    refl
    "10.1103/PhysRevD.105.012010"
    refl
    "HEPData-style public record or explicit no-HEPData-record attestation must be bound before projection"
    "branching-fraction table/row for B(Bs0 -> mu+ mu-) must be bound before projection"
    "checksum or digest for the cited table payload must be bound before projection"
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
