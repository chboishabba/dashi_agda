module DASHI.Physics.Closure.YMSprint109NoBottomSpectrumPollutionCompactness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge
  as Mosco108
import DASHI.Physics.Closure.YMSprint108SpectralGapTransport
  as Spectral108
import DASHI.Physics.Closure.YMSprint108UniformFormLowerBound
  as Form108

------------------------------------------------------------------------
-- Sprint 109 no-bottom-spectrum-pollution compactness ledger.
--
-- This module narrows the Sprint108 continuum-passage boundary to the
-- compactness/tightness ingredient that may feed no-spectral-pollution, but
-- does not by itself prove it.  The corrected split is explicit:
--
--   * Mosco/compactness/tightness are necessary support inputs.
--   * H3a is the hard transfer-matrix / norm-resolvent convergence theorem on
--     the vacuum-orthogonal sector.
--   * H3b is RP.4 / OS vacuum-projection continuity for the limiting vacuum.
--   * No-spectral-pollution depends on H3a + H3b, not on Mosco alone.
--
-- It records the exact relation between tight finite low-energy branches,
-- compact extraction in the physical carrier, vacuum-sector isolation, the
-- open H3a/H3b interfaces, and the still-open no-collapse-at-zero theorem.
-- It is concrete and checked: the theorem and Clay promotion flags are
-- explicitly false, with equality witnesses, while the next analytic
-- requirements are first-class values.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

compactnessLedgerRecorded : Bool
compactnessLedgerRecorded = true

noBottomSpectrumPollutionCompactnessTheoremProved : Bool
noBottomSpectrumPollutionCompactnessTheoremProved = false

tightnessCriterionProvedHere : Bool
tightnessCriterionProvedHere = false

compactEmbeddingProvedHere : Bool
compactEmbeddingProvedHere = false

spuriousBottomEigenbranchesExcludedHere : Bool
spuriousBottomEigenbranchesExcludedHere = false

isolatedBottomSectorIdentifiedHere : Bool
isolatedBottomSectorIdentifiedHere = false

bottomSectorProjectionConvergenceProvedHere : Bool
bottomSectorProjectionConvergenceProvedHere = false

rp4LimitingVacuumIdentityAvailableHere : Bool
rp4LimitingVacuumIdentityAvailableHere = false

h3aTransferMatrixConvergenceProvedHere : Bool
h3aTransferMatrixConvergenceProvedHere = false

h3bVacuumProjectionContinuityProvedHere : Bool
h3bVacuumProjectionContinuityProvedHere = false

noCollapseAtZeroProvedHere : Bool
noCollapseAtZeroProvedHere = false

moscoNoPollutionImported : Bool
moscoNoPollutionImported =
  Mosco108.bridgeReceiptRecorded

spectralTransportImported : Bool
spectralTransportImported =
  Spectral108.spectralGapTransportRecorded

uniformFormLedgerImported : Bool
uniformFormLedgerImported =
  Form108.uniformFormLedgerRecorded

finiteSupportEnoughForCompactness : Bool
finiteSupportEnoughForCompactness = false

compactnessEnoughWithoutBottomIsolation : Bool
compactnessEnoughWithoutBottomIsolation = false

noCollapseAtZeroClosedStatus : Bool
noCollapseAtZeroClosedStatus = false

targetNoPollutionText : String
targetNoPollutionText =
  "Every finite low-energy non-vacuum eigenbranch that is tight may feed a no-spectral-pollution argument only after H3a supplies vacuum-orthogonal transfer-matrix / norm-resolvent convergence and H3b supplies RP.4 / OS vacuum-projection continuity for the limiting vacuum."

tightnessText : String
tightnessText =
  "Tightness requirement: normalized finite low-energy vectors must have uniformly controlled physical tails, gauge-sector leakage, and form energy across 0 < a <= a0."

compactnessText : String
compactnessText =
  "Compactness requirement: tight bounded-energy branches must admit strongly convergent subsequences in the physical carrier after the finite-to-continuum identification; compactness and Mosco liminf are necessary support only and do not determine the vacuum sector or exclude spectral pollution by themselves."

spuriousBranchExclusionText : String
spuriousBranchExclusionText =
  "Spurious bottom eigenbranch exclusion: an eigenvalue branch not converging to the physical vacuum sector may not accumulate below the first continuum threshold only after H3a fixes the vacuum-orthogonal transfer limit and H3b fixes the RP.4 / OS vacuum projection being excluded."

isolatedBottomSectorRelationText : String
isolatedBottomSectorRelationText =
  "The isolated bottom sector supplies the separated vacuum projection; compactness only becomes part of a no-pollution theorem after H3b identifies convergence of finite vacuum projections to the RP.4 / OS limiting vacuum and after the first excited threshold is identified on the same carrier."

noCollapseAtZeroStatusText : String
noCollapseAtZeroStatusText =
  "No-collapse-at-zero is recorded as open: non-vacuum eigenvalue sequences are not yet proved to stay uniformly away from zero in the continuum limit."

finiteSupportLimitationText : String
finiteSupportLimitationText =
  "Finite transfer positivity and finite support are imported Sprint108 support, but they do not provide tightness, compact extraction, or exclusion of bottom-spectrum pollution."

nextAnalyticRequirementsText : String
nextAnalyticRequirementsText =
  "Next requirements: prove tail tightness and compact carrier extraction as support inputs, then prove H3a vacuum-orthogonal transfer-matrix / norm-resolvent convergence, prove H3b RP.4 / OS vacuum-projection continuity, identify the first excited threshold, and exclude zero collapse by a uniform non-vacuum lower bound."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint109 records compactness obligations only; it does not prove H3a, does not prove H3b, does not prove no-spectral-pollution, does not promote Clay Yang-Mills, and does not close the continuum Hamiltonian mass-gap theorem."

sprint108MoscoPath : String
sprint108MoscoPath =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

sprint108SpectralTransportPath : String
sprint108SpectralTransportPath =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

sprint108UniformFormPath : String
sprint108UniformFormPath =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

data CompactnessLane : Set where
  tightness-of-low-energy-branches :
    CompactnessLane
  compact-physical-extraction :
    CompactnessLane
  h3a-vacuum-orthogonal-transfer :
    CompactnessLane
  h3b-vacuum-projection-continuity :
    CompactnessLane
  spurious-bottom-branch-exclusion :
    CompactnessLane
  isolated-bottom-sector-relation :
    CompactnessLane
  no-collapse-at-zero-status :
    CompactnessLane
  finite-support-limitation :
    CompactnessLane
  next-analytic-requirements :
    CompactnessLane

data CompactnessStatus : Set where
  imported-sprint108-support :
    CompactnessStatus
  required-tightness-not-proved :
    CompactnessStatus
  required-compactness-not-proved :
    CompactnessStatus
  h3a-required-not-proved :
    CompactnessStatus
  h3b-required-not-proved :
    CompactnessStatus
  required-branch-exclusion-not-proved :
    CompactnessStatus
  bottom-sector-relation-recorded :
    CompactnessStatus
  no-collapse-at-zero-open :
    CompactnessStatus
  finite-support-insufficient :
    CompactnessStatus
  theorem-open :
    CompactnessStatus
  nonpromotion :
    CompactnessStatus

record Sprint108CompactnessInputs : Setω where
  constructor mkSprint108CompactnessInputs
  field
    moscoNoPollutionReceipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    spectralGapTransportReceipt :
      Spectral108.YMSprint108SpectralGapTransportReceipt
    uniformFormLowerBoundReceipt :
      Form108.YMSprint108UniformFormLowerBoundReceipt
    moscoPath :
      String
    spectralTransportPath :
      String
    uniformFormPath :
      String
    moscoNoBottomPollutionProved :
      Bool
    spectralNoCollapseAtZeroProved :
      Bool
    uniformContinuumPassageProved :
      Bool
    importedSupportRecorded :
      Bool

record TightnessCriterionStatus : Set where
  constructor mkTightnessCriterionStatus
  field
    lane :
      CompactnessLane
    statement :
      String
    lowEnergyBranchesControlled :
      Bool
    physicalTailControlRequired :
      Bool
    gaugeSectorLeakageControlRequired :
      Bool
    uniformFormEnergyBoundRequired :
      Bool
    provedHere :
      Bool
    status :
      CompactnessStatus

record CompactExtractionStatus : Set where
  constructor mkCompactExtractionStatus
  field
    lane :
      CompactnessLane
    statement :
      String
    tightnessInputRequired :
      Bool
    carrierIdentificationRequired :
      Bool
    strongSubsequenceConvergenceRequired :
      Bool
    provedHere :
      Bool
    status :
      CompactnessStatus

record SpuriousBottomEigenbranchExclusionStatus : Set where
  constructor mkSpuriousBottomEigenbranchExclusionStatus
  field
    lane :
      CompactnessLane
    statement :
      String
    compactExtractionRequired :
      Bool
    moscoLiminfRequired :
      Bool
    isolatedBottomSectorRequired :
      Bool
    thresholdIdentificationRequired :
      Bool
    excludedHere :
      Bool
    status :
      CompactnessStatus

record IsolatedBottomSectorRelationStatus : Set where
  constructor mkIsolatedBottomSectorRelationStatus
  field
    lane :
      CompactnessLane
    statement :
      String
    importedSprint108SectorRecord :
      Bool
    vacuumProjectionSeparationRequired :
      Bool
    bottomSectorProjectionConvergenceRequired :
      Bool
    limitingVacuumIdentityRequired :
      Bool
    firstThresholdTransportRequired :
      Bool
    compactnessAloneEnough :
      Bool
    identifiedHere :
      Bool
    status :
      CompactnessStatus

record NoCollapseAtZeroExactStatus : Set where
  constructor mkNoCollapseAtZeroExactStatus
  field
    lane :
      CompactnessLane
    statement :
      String
    recordedBySprint108 :
      Bool
    requiredForContinuumMassGap :
      Bool
    followsFromFiniteSupportAlone :
      Bool
    closedHere :
      Bool
    closedStatus :
      Bool
    status :
      CompactnessStatus

record FiniteSupportCompactnessLimitation : Set where
  constructor mkFiniteSupportCompactnessLimitation
  field
    lane :
      CompactnessLane
    statement :
      String
    finiteSupportImported :
      Bool
    enoughForTightness :
      Bool
    enoughForCompactExtraction :
      Bool
    enoughForNoPollution :
      Bool
    status :
      CompactnessStatus

record NextAnalyticRequirement : Set where
  constructor mkNextAnalyticRequirement
  field
    lane :
      CompactnessLane
    requirement :
      String
    requiredForNoPollution :
      Bool
    dischargedHere :
      Bool
    status :
      CompactnessStatus

record NoPollutionCompactnessTheoremBoundary : Set where
  constructor mkNoPollutionCompactnessTheoremBoundary
  field
    target :
      String
    tightnessProved :
      Bool
    compactEmbeddingProved :
      Bool
    spuriousBranchesExcluded :
      Bool
    isolatedBottomSectorIdentified :
      Bool
    h3aTransferMatrixConvergenceProved :
      Bool
    h3bVacuumProjectionContinuityProved :
      Bool
    bottomSectorProjectionConvergenceProved :
      Bool
    limitingVacuumIdentityAvailable :
      Bool
    noCollapseAtZeroProved :
      Bool
    finiteSupportEnough :
      Bool
    moscoCompactnessNecessaryButInsufficient :
      Bool
    theoremProvedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    status :
      CompactnessStatus

record YMSprint109NoBottomSpectrumPollutionCompactnessReceipt : Setω where
  field
    sprint108Inputs :
      Sprint108CompactnessInputs
    tightnessCriterion :
      TightnessCriterionStatus
    compactExtraction :
      CompactExtractionStatus
    spuriousBottomEigenbranchExclusion :
      SpuriousBottomEigenbranchExclusionStatus
    isolatedBottomSectorRelation :
      IsolatedBottomSectorRelationStatus
    noCollapseAtZero :
      NoCollapseAtZeroExactStatus
    finiteSupportLimitation :
      FiniteSupportCompactnessLimitation
    nextAnalyticRequirements :
      List NextAnalyticRequirement
    theoremBoundary :
      NoPollutionCompactnessTheoremBoundary
    ledgerText :
      List String
    receiptRecorded :
      Bool
    theoremProvedHereFlag :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHereFlag ≡ false
    noCollapseAtZeroClosedFlag :
      Bool
    noCollapseAtZeroClosedFlagIsFalse :
      noCollapseAtZeroClosedFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint109NoBottomSpectrumPollutionCompactnessReceipt public

canonicalSprint108CompactnessInputs :
  Sprint108CompactnessInputs
canonicalSprint108CompactnessInputs =
  mkSprint108CompactnessInputs
    Mosco108.canonicalReceipt
    Spectral108.canonicalReceipt
    Form108.canonicalReceipt
    sprint108MoscoPath
    sprint108SpectralTransportPath
    sprint108UniformFormPath
    Mosco108.canonicalReceiptNoBottomPollutionProvedHere
    Spectral108.noEigenvalueCollapseAtZeroProvedHere
    Form108.continuumSpectralPassageProvedHere
    true

canonicalTightnessCriterionStatus :
  TightnessCriterionStatus
canonicalTightnessCriterionStatus =
  mkTightnessCriterionStatus
    tightness-of-low-energy-branches
    tightnessText
    true
    true
    true
    true
    tightnessCriterionProvedHere
    required-tightness-not-proved

canonicalCompactExtractionStatus :
  CompactExtractionStatus
canonicalCompactExtractionStatus =
  mkCompactExtractionStatus
    compact-physical-extraction
    compactnessText
    true
    true
    true
    compactEmbeddingProvedHere
    required-compactness-not-proved

canonicalSpuriousBottomEigenbranchExclusionStatus :
  SpuriousBottomEigenbranchExclusionStatus
canonicalSpuriousBottomEigenbranchExclusionStatus =
  mkSpuriousBottomEigenbranchExclusionStatus
    spurious-bottom-branch-exclusion
    spuriousBranchExclusionText
    true
    true
    true
    true
    spuriousBottomEigenbranchesExcludedHere
    required-branch-exclusion-not-proved

canonicalIsolatedBottomSectorRelationStatus :
  IsolatedBottomSectorRelationStatus
canonicalIsolatedBottomSectorRelationStatus =
  mkIsolatedBottomSectorRelationStatus
    isolated-bottom-sector-relation
    isolatedBottomSectorRelationText
    Spectral108.isolatedBottomSectorRecorded
    true
    true
    true
    true
    compactnessEnoughWithoutBottomIsolation
    isolatedBottomSectorIdentifiedHere
    bottom-sector-relation-recorded

canonicalNoCollapseAtZeroExactStatus :
  NoCollapseAtZeroExactStatus
canonicalNoCollapseAtZeroExactStatus =
  mkNoCollapseAtZeroExactStatus
    no-collapse-at-zero-status
    noCollapseAtZeroStatusText
    Spectral108.noEigenvalueCollapseAtZeroRecorded
    true
    false
    noCollapseAtZeroProvedHere
    noCollapseAtZeroClosedStatus
    no-collapse-at-zero-open

canonicalFiniteSupportCompactnessLimitation :
  FiniteSupportCompactnessLimitation
canonicalFiniteSupportCompactnessLimitation =
  mkFiniteSupportCompactnessLimitation
    finite-support-limitation
    finiteSupportLimitationText
    moscoNoPollutionImported
    finiteSupportEnoughForCompactness
    false
    false
    finite-support-insufficient

tailTightnessRequirement : NextAnalyticRequirement
tailTightnessRequirement =
  mkNextAnalyticRequirement
    next-analytic-requirements
    "Prove uniform physical-tail tightness for normalized finite low-energy branches."
    true
    false
    required-tightness-not-proved

compactCarrierExtractionRequirement : NextAnalyticRequirement
compactCarrierExtractionRequirement =
  mkNextAnalyticRequirement
    next-analytic-requirements
    "Prove compact extraction in the continuum physical carrier for tight bounded-form-energy branches."
    true
    false
    required-compactness-not-proved

h3aVacuumOrthogonalTransferRequirement : NextAnalyticRequirement
h3aVacuumOrthogonalTransferRequirement =
  mkNextAnalyticRequirement
    h3a-vacuum-orthogonal-transfer
    "Prove H3a: transfer-matrix / norm-resolvent convergence on T_N restricted to the vacuum-orthogonal sector; Mosco liminf and compactness do not supply this upgrade."
    true
    false
    h3a-required-not-proved

h3bVacuumProjectionContinuityRequirement : NextAnalyticRequirement
h3bVacuumProjectionContinuityRequirement =
  mkNextAnalyticRequirement
    h3b-vacuum-projection-continuity
    "Prove H3b: RP.4 / OS vacuum-projection continuity for the limiting vacuum; compactness alone does not identify or transport the correct vacuum projector."
    true
    false
    h3b-required-not-proved

bottomProjectionConvergenceRequirement : NextAnalyticRequirement
bottomProjectionConvergenceRequirement =
  mkNextAnalyticRequirement
    h3b-vacuum-projection-continuity
    "Identify convergence of the finite vacuum projection to the isolated continuum bottom-sector projection as a concrete H3b sub-obligation on the RP.4 / OS vacuum sector."
    true
    false
    h3b-required-not-proved

limitingVacuumIdentityRequirement : NextAnalyticRequirement
limitingVacuumIdentityRequirement =
  mkNextAnalyticRequirement
    h3b-vacuum-projection-continuity
    "Identify the isolated limiting vacuum itself, in RP.4 / OS form, so compactly convergent low-energy branches can be tested against the correct vacuum sector."
    true
    false
    h3b-required-not-proved

thresholdIdentificationRequirement : NextAnalyticRequirement
thresholdIdentificationRequirement =
  mkNextAnalyticRequirement
    next-analytic-requirements
    "Transport and identify the first excited threshold after finite-to-continuum spectral passage."
    true
    false
    required-branch-exclusion-not-proved

zeroCollapseExclusionRequirement : NextAnalyticRequirement
zeroCollapseExclusionRequirement =
  mkNextAnalyticRequirement
    next-analytic-requirements
    "Prove a uniform non-vacuum lower bound that excludes eigenvalue collapse at zero."
    true
    false
    no-collapse-at-zero-open

canonicalNextAnalyticRequirements :
  List NextAnalyticRequirement
canonicalNextAnalyticRequirements =
  tailTightnessRequirement
  ∷ compactCarrierExtractionRequirement
  ∷ h3aVacuumOrthogonalTransferRequirement
  ∷ h3bVacuumProjectionContinuityRequirement
  ∷ bottomProjectionConvergenceRequirement
  ∷ limitingVacuumIdentityRequirement
  ∷ thresholdIdentificationRequirement
  ∷ zeroCollapseExclusionRequirement
  ∷ []

canonicalTheoremBoundary :
  NoPollutionCompactnessTheoremBoundary
canonicalTheoremBoundary =
  mkNoPollutionCompactnessTheoremBoundary
    targetNoPollutionText
    tightnessCriterionProvedHere
    compactEmbeddingProvedHere
    spuriousBottomEigenbranchesExcludedHere
    isolatedBottomSectorIdentifiedHere
    h3aTransferMatrixConvergenceProvedHere
    h3bVacuumProjectionContinuityProvedHere
    bottomSectorProjectionConvergenceProvedHere
    rp4LimitingVacuumIdentityAvailableHere
    noCollapseAtZeroProvedHere
    finiteSupportEnoughForCompactness
    true
    noBottomSpectrumPollutionCompactnessTheoremProved
    clayYangMillsPromoted
    theorem-open

canonicalYMSprint109NoBottomSpectrumPollutionCompactnessReceipt :
  YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
canonicalYMSprint109NoBottomSpectrumPollutionCompactnessReceipt =
  record
    { sprint108Inputs =
        canonicalSprint108CompactnessInputs
    ; tightnessCriterion =
        canonicalTightnessCriterionStatus
    ; compactExtraction =
        canonicalCompactExtractionStatus
    ; spuriousBottomEigenbranchExclusion =
        canonicalSpuriousBottomEigenbranchExclusionStatus
    ; isolatedBottomSectorRelation =
        canonicalIsolatedBottomSectorRelationStatus
    ; noCollapseAtZero =
        canonicalNoCollapseAtZeroExactStatus
    ; finiteSupportLimitation =
        canonicalFiniteSupportCompactnessLimitation
    ; nextAnalyticRequirements =
        canonicalNextAnalyticRequirements
    ; theoremBoundary =
        canonicalTheoremBoundary
    ; ledgerText =
        targetNoPollutionText
        ∷ tightnessText
        ∷ compactnessText
        ∷ spuriousBranchExclusionText
        ∷ isolatedBottomSectorRelationText
        ∷ noCollapseAtZeroStatusText
        ∷ finiteSupportLimitationText
        ∷ nextAnalyticRequirementsText
        ∷ nonPromotionBoundaryText
        ∷ []
    ; receiptRecorded =
        compactnessLedgerRecorded
    ; theoremProvedHereFlag =
        noBottomSpectrumPollutionCompactnessTheoremProved
    ; theoremProvedHereIsFalse =
        refl
    ; noCollapseAtZeroClosedFlag =
        noCollapseAtZeroClosedStatus
    ; noCollapseAtZeroClosedFlagIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    }

canonicalReceipt :
  YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
canonicalReceipt =
  canonicalYMSprint109NoBottomSpectrumPollutionCompactnessReceipt

canonicalReceiptNoBottomSpectrumPollutionTheoremNotProved :
  theoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptNoBottomSpectrumPollutionTheoremNotProved =
  refl

canonicalReceiptNoCollapseAtZeroStillOpen :
  noCollapseAtZeroClosedFlag canonicalReceipt ≡ false
canonicalReceiptNoCollapseAtZeroStillOpen =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
