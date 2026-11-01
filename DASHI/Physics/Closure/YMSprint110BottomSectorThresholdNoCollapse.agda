module DASHI.Physics.Closure.YMSprint110BottomSectorThresholdNoCollapse where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint108SpectralGapTransport
  as Spectral108
import DASHI.Physics.Closure.YMSprint109NoBottomSpectrumPollutionCompactness
  as Compactness109

------------------------------------------------------------------------
-- Sprint 110 bottom-sector threshold/no-collapse ledger.
--
-- This module advances the Sprint108 spectral-transport boundary and the
-- Sprint109 compactness/no-bottom-pollution ledger into the exact downstream
-- status surface for:
--
--   * isolated vacuum/bottom sector;
--   * first-excited threshold identification;
--   * finite vacuum-projection convergence;
--   * spurious branch exclusion criterion;
--   * no-collapse-at-zero status.
--
-- It is intentionally fail-closed.  The criteria and imported dependencies
-- are concrete receipt values, but the analytic theorems are not claimed here,
-- and Clay Yang-Mills is not promoted.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

bottomSectorThresholdLedgerRecorded : Bool
bottomSectorThresholdLedgerRecorded = true

bottomSectorThresholdTheoremProvedHere : Bool
bottomSectorThresholdTheoremProvedHere = false

isolatedVacuumBottomSectorProvedHere : Bool
isolatedVacuumBottomSectorProvedHere = false

firstExcitedThresholdIdentifiedHere : Bool
firstExcitedThresholdIdentifiedHere = false

projectionConvergenceProvedHere : Bool
projectionConvergenceProvedHere = false

spuriousBranchesExcludedHere : Bool
spuriousBranchesExcludedHere = false

spuriousBranchExclusionCriterionRecorded : Bool
spuriousBranchExclusionCriterionRecorded = true

noCollapseAtZeroProvedHere : Bool
noCollapseAtZeroProvedHere = false

noCollapseAtZeroClosed : Bool
noCollapseAtZeroClosed = false

continuumHamiltonianGapProvedHere : Bool
continuumHamiltonianGapProvedHere = false

spectral108Imported : Bool
spectral108Imported =
  Spectral108.spectralGapTransportRecorded

compactness109Imported : Bool
compactness109Imported =
  Compactness109.compactnessLedgerRecorded

projectionConvergenceFollowsFromCompactnessAlone : Bool
projectionConvergenceFollowsFromCompactnessAlone = false

thresholdIdentificationFollowsFromFiniteGapAlone : Bool
thresholdIdentificationFollowsFromFiniteGapAlone = false

branchExclusionFollowsFromCriterionAlone : Bool
branchExclusionFollowsFromCriterionAlone = false

noCollapseFollowsFromBottomIsolationAlone : Bool
noCollapseFollowsFromBottomIsolationAlone = false

spectral108Path : String
spectral108Path =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

compactness109Path : String
compactness109Path =
  "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda"

targetText : String
targetText =
  "Identify the isolated vacuum bottom sector and first excited threshold, then exclude tight non-vacuum finite branches from collapsing to zero or polluting the bottom spectrum."

isolatedVacuumBottomSectorText : String
isolatedVacuumBottomSectorText =
  "The continuum physical Hamiltonian must have a separated vacuum bottom sector whose projection is the limit target for finite vacuum projections."

firstExcitedThresholdIdentificationText : String
firstExcitedThresholdIdentificationText =
  "The first excited threshold is the spectral edge above the isolated vacuum sector after finite-to-continuum spectral passage, Mosco liminf, and no-bottom-pollution are available."

projectionConvergenceText : String
projectionConvergenceText =
  "Projection convergence requires finite vacuum-sector projections to converge to the isolated continuum bottom-sector projection under the physical carrier identification."

spuriousBranchExclusionCriterionText : String
spuriousBranchExclusionCriterionText =
  "Criterion: a normalized tight finite eigenbranch that is asymptotically orthogonal to the finite vacuum projection and whose compact physical limit is non-vacuum must not accumulate below the identified first excited threshold."

noCollapseAtZeroStatusText : String
noCollapseAtZeroStatusText =
  "No-collapse-at-zero remains open: a uniform positive lower bound for non-vacuum branches is recorded as required, not proved."

dependencyBoundaryText : String
dependencyBoundaryText =
  "Sprint110 consumes Sprint108 spectral transport and Sprint109 no-bottom compactness receipts; finite transfer positivity, compactness, or bottom isolation alone do not close the theorem."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint110 records threshold/no-collapse criteria only and does not promote the continuum Hamiltonian gap or Clay Yang-Mills."

data BottomThresholdLane : Set where
  isolated-vacuum-bottom-sector :
    BottomThresholdLane
  first-excited-threshold-identification :
    BottomThresholdLane
  projection-convergence :
    BottomThresholdLane
  spurious-branch-exclusion-criterion :
    BottomThresholdLane
  no-collapse-at-zero-status :
    BottomThresholdLane
  theorem-boundary :
    BottomThresholdLane

data BottomThresholdStatus : Set where
  imported-sprint108-spectral-support :
    BottomThresholdStatus
  imported-sprint109-compactness-support :
    BottomThresholdStatus
  isolated-sector-required :
    BottomThresholdStatus
  threshold-identification-required :
    BottomThresholdStatus
  projection-convergence-required :
    BottomThresholdStatus
  exclusion-criterion-recorded :
    BottomThresholdStatus
  no-collapse-at-zero-open :
    BottomThresholdStatus
  theorem-open :
    BottomThresholdStatus
  nonpromotion :
    BottomThresholdStatus

record Sprint108SpectralInput : Setω where
  constructor mkSprint108SpectralInput
  field
    receipt :
      Spectral108.YMSprint108SpectralGapTransportReceipt
    modulePath :
      String
    imported :
      Bool
    isolatedBottomSectorRecorded :
      Bool
    firstThresholdTransportRecorded :
      Bool
    noCollapseAtZeroRecorded :
      Bool
    transportTheoremProved :
      Bool
    transportTheoremProvedIsFalse :
      transportTheoremProved ≡ false

record Sprint109CompactnessInput : Setω where
  constructor mkSprint109CompactnessInput
  field
    receipt :
      Compactness109.YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
    modulePath :
      String
    imported :
      Bool
    tightnessProved :
      Bool
    compactExtractionProved :
      Bool
    spuriousBranchesExcluded :
      Bool
    noCollapseClosed :
      Bool
    noCollapseClosedIsFalse :
      noCollapseClosed ≡ false

record IsolatedVacuumBottomSector : Set where
  constructor mkIsolatedVacuumBottomSector
  field
    lane :
      BottomThresholdLane
    statement :
      String
    importedSpectralRecord :
      Bool
    vacuumProjectionSeparatedRequired :
      Bool
    bottomSectorIsolationRequired :
      Bool
    identifiedHere :
      Bool
    provedHere :
      Bool
    status :
      BottomThresholdStatus

record FirstExcitedThresholdIdentification : Set where
  constructor mkFirstExcitedThresholdIdentification
  field
    lane :
      BottomThresholdLane
    statement :
      String
    spectralTransportRequired :
      Bool
    moscoLiminfRequired :
      Bool
    noBottomPollutionRequired :
      Bool
    projectionConvergenceRequired :
      Bool
    followsFromFiniteGapAlone :
      Bool
    identifiedHere :
      Bool
    status :
      BottomThresholdStatus

record ProjectionConvergenceStatus : Set where
  constructor mkProjectionConvergenceStatus
  field
    lane :
      BottomThresholdLane
    statement :
      String
    finiteVacuumProjectionRequired :
      Bool
    continuumBottomProjectionRequired :
      Bool
    carrierIdentificationRequired :
      Bool
    compactnessInputRequired :
      Bool
    isolatedSectorInputRequired :
      Bool
    followsFromCompactnessAlone :
      Bool
    provedHere :
      Bool
    status :
      BottomThresholdStatus

record SpuriousBranchExclusionCriterion : Set where
  constructor mkSpuriousBranchExclusionCriterion
  field
    lane :
      BottomThresholdLane
    statement :
      String
    normalizedTightEigenbranchRequired :
      Bool
    asymptoticVacuumOrthogonalityRequired :
      Bool
    compactPhysicalLimitRequired :
      Bool
    nonVacuumLimitRequired :
      Bool
    thresholdComparisonRequired :
      Bool
    criterionRecorded :
      Bool
    branchesExcludedHere :
      Bool
    theoremFollowsFromCriterionAlone :
      Bool
    status :
      BottomThresholdStatus

record NoCollapseAtZeroStatus : Set where
  constructor mkNoCollapseAtZeroStatus
  field
    lane :
      BottomThresholdLane
    statement :
      String
    importedSpectralRecord :
      Bool
    importedCompactnessRecord :
      Bool
    nonVacuumLowerBoundRequired :
      Bool
    thresholdIdentificationRequired :
      Bool
    followsFromBottomIsolationAlone :
      Bool
    provedHere :
      Bool
    closed :
      Bool
    status :
      BottomThresholdStatus

record BottomSectorThresholdTheoremBoundary : Set where
  constructor mkBottomSectorThresholdTheoremBoundary
  field
    lane :
      BottomThresholdLane
    target :
      String
    isolatedVacuumBottomSectorProved :
      Bool
    firstExcitedThresholdIdentified :
      Bool
    projectionConvergenceProved :
      Bool
    spuriousBranchCriterionRecorded :
      Bool
    spuriousBranchesExcluded :
      Bool
    noCollapseAtZeroProved :
      Bool
    continuumHamiltonianGapProved :
      Bool
    theoremProvedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    status :
      BottomThresholdStatus

record YMSprint110BottomSectorThresholdNoCollapseReceipt : Setω where
  field
    sprint108SpectralInput :
      Sprint108SpectralInput
    sprint109CompactnessInput :
      Sprint109CompactnessInput
    isolatedVacuumBottomSector :
      IsolatedVacuumBottomSector
    firstExcitedThresholdIdentification :
      FirstExcitedThresholdIdentification
    projectionConvergence :
      ProjectionConvergenceStatus
    spuriousBranchExclusionCriterion :
      SpuriousBranchExclusionCriterion
    noCollapseAtZero :
      NoCollapseAtZeroStatus
    theoremBoundary :
      BottomSectorThresholdTheoremBoundary
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

open YMSprint110BottomSectorThresholdNoCollapseReceipt public

canonicalSprint108SpectralInput :
  Sprint108SpectralInput
canonicalSprint108SpectralInput =
  mkSprint108SpectralInput
    Spectral108.canonicalReceipt
    spectral108Path
    spectral108Imported
    Spectral108.isolatedBottomSectorRecorded
    Spectral108.firstExcitedThresholdTransportRecorded
    Spectral108.noEigenvalueCollapseAtZeroRecorded
    Spectral108.transportTheoremProvedHere
    refl

canonicalSprint109CompactnessInput :
  Sprint109CompactnessInput
canonicalSprint109CompactnessInput =
  mkSprint109CompactnessInput
    Compactness109.canonicalReceipt
    compactness109Path
    compactness109Imported
    Compactness109.tightnessCriterionProvedHere
    Compactness109.compactEmbeddingProvedHere
    Compactness109.spuriousBottomEigenbranchesExcludedHere
    Compactness109.noCollapseAtZeroClosedStatus
    refl

canonicalIsolatedVacuumBottomSector :
  IsolatedVacuumBottomSector
canonicalIsolatedVacuumBottomSector =
  mkIsolatedVacuumBottomSector
    isolated-vacuum-bottom-sector
    isolatedVacuumBottomSectorText
    Spectral108.isolatedBottomSectorRecorded
    true
    true
    false
    isolatedVacuumBottomSectorProvedHere
    isolated-sector-required

canonicalFirstExcitedThresholdIdentification :
  FirstExcitedThresholdIdentification
canonicalFirstExcitedThresholdIdentification =
  mkFirstExcitedThresholdIdentification
    first-excited-threshold-identification
    firstExcitedThresholdIdentificationText
    Spectral108.firstExcitedThresholdTransportRecorded
    true
    true
    true
    thresholdIdentificationFollowsFromFiniteGapAlone
    firstExcitedThresholdIdentifiedHere
    threshold-identification-required

canonicalProjectionConvergenceStatus :
  ProjectionConvergenceStatus
canonicalProjectionConvergenceStatus =
  mkProjectionConvergenceStatus
    projection-convergence
    projectionConvergenceText
    true
    true
    true
    true
    true
    projectionConvergenceFollowsFromCompactnessAlone
    projectionConvergenceProvedHere
    projection-convergence-required

canonicalSpuriousBranchExclusionCriterion :
  SpuriousBranchExclusionCriterion
canonicalSpuriousBranchExclusionCriterion =
  mkSpuriousBranchExclusionCriterion
    spurious-branch-exclusion-criterion
    spuriousBranchExclusionCriterionText
    true
    true
    true
    true
    true
    spuriousBranchExclusionCriterionRecorded
    spuriousBranchesExcludedHere
    branchExclusionFollowsFromCriterionAlone
    exclusion-criterion-recorded

canonicalNoCollapseAtZeroStatus :
  NoCollapseAtZeroStatus
canonicalNoCollapseAtZeroStatus =
  mkNoCollapseAtZeroStatus
    no-collapse-at-zero-status
    noCollapseAtZeroStatusText
    Spectral108.noEigenvalueCollapseAtZeroRecorded
    true
    true
    true
    noCollapseFollowsFromBottomIsolationAlone
    noCollapseAtZeroProvedHere
    noCollapseAtZeroClosed
    no-collapse-at-zero-open

canonicalTheoremBoundary :
  BottomSectorThresholdTheoremBoundary
canonicalTheoremBoundary =
  mkBottomSectorThresholdTheoremBoundary
    theorem-boundary
    targetText
    isolatedVacuumBottomSectorProvedHere
    firstExcitedThresholdIdentifiedHere
    projectionConvergenceProvedHere
    spuriousBranchExclusionCriterionRecorded
    spuriousBranchesExcludedHere
    noCollapseAtZeroProvedHere
    continuumHamiltonianGapProvedHere
    bottomSectorThresholdTheoremProvedHere
    clayYangMillsPromoted
    theorem-open

canonicalYMSprint110BottomSectorThresholdNoCollapseReceipt :
  YMSprint110BottomSectorThresholdNoCollapseReceipt
canonicalYMSprint110BottomSectorThresholdNoCollapseReceipt =
  record
    { sprint108SpectralInput =
        canonicalSprint108SpectralInput
    ; sprint109CompactnessInput =
        canonicalSprint109CompactnessInput
    ; isolatedVacuumBottomSector =
        canonicalIsolatedVacuumBottomSector
    ; firstExcitedThresholdIdentification =
        canonicalFirstExcitedThresholdIdentification
    ; projectionConvergence =
        canonicalProjectionConvergenceStatus
    ; spuriousBranchExclusionCriterion =
        canonicalSpuriousBranchExclusionCriterion
    ; noCollapseAtZero =
        canonicalNoCollapseAtZeroStatus
    ; theoremBoundary =
        canonicalTheoremBoundary
    ; ledgerText =
        targetText
        ∷ isolatedVacuumBottomSectorText
        ∷ firstExcitedThresholdIdentificationText
        ∷ projectionConvergenceText
        ∷ spuriousBranchExclusionCriterionText
        ∷ noCollapseAtZeroStatusText
        ∷ dependencyBoundaryText
        ∷ nonPromotionBoundaryText
        ∷ []
    ; receiptRecorded =
        bottomSectorThresholdLedgerRecorded
    ; theoremProvedHereFlag =
        bottomSectorThresholdTheoremProvedHere
    ; theoremProvedHereIsFalse =
        refl
    ; noCollapseAtZeroClosedFlag =
        noCollapseAtZeroClosed
    ; noCollapseAtZeroClosedFlagIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    }

canonicalReceipt :
  YMSprint110BottomSectorThresholdNoCollapseReceipt
canonicalReceipt =
  canonicalYMSprint110BottomSectorThresholdNoCollapseReceipt

canonicalReceiptTheoremNotProved :
  theoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptTheoremNotProved =
  refl

canonicalReceiptNoCollapseAtZeroStillOpen :
  noCollapseAtZeroClosedFlag canonicalReceipt ≡ false
canonicalReceiptNoCollapseAtZeroStillOpen =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalSpuriousBranchCriterionRecorded :
  SpuriousBranchExclusionCriterion.criterionRecorded
    (spuriousBranchExclusionCriterion canonicalReceipt) ≡ true
canonicalSpuriousBranchCriterionRecorded =
  refl
