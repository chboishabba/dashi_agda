module DASHI.Physics.Closure.YMSprint119MoscoAllObligationsReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint118MoscoCompactnessReadinessAggregator
  as Sprint118
import DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge
  as Mosco108
import DASHI.Physics.Closure.YMSprint109NoBottomSpectrumPollutionCompactness
  as Compact109
import DASHI.Physics.Closure.YMSprint110BottomSectorThresholdNoCollapse
  as Collapse110
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion
  as Closed110
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110

------------------------------------------------------------------------
-- Sprint119 Mosco all-obligations reducer.
--
-- This reducer now separates the genuine Mosco package from the stronger
-- continuum-transfer obligations.  The five Mosco gates only certify form
-- compactness, liminf control, and recovery data.  They do not by themselves
-- force survival of a positive spectral margin.  Gap survival is recorded as
-- downstream H3a/H3b work:
--
--   H3a : trace / norm-resolvent control on the vacuum-orthogonal transfer
--         sector, strong enough to exclude spectral pollution.
--   H3b : vacuum-projection continuity, downstream of H3a plus RP.4.
--
-- No-spectral-pollution is therefore downstream of both H3a and H3b rather
-- than a direct consequence of Mosco compactness.

sprintNumber : Nat
sprintNumber = 119

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint119MoscoAllObligationsReducer.agda"

sprint118SourcePath : String
sprint118SourcePath =
  "DASHI/Physics/Closure/YMSprint118MoscoCompactnessReadinessAggregator.agda"

mosco108SourcePath : String
mosco108SourcePath =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

compact109SourcePath : String
compact109SourcePath =
  "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda"

collapse110SourcePath : String
collapse110SourcePath =
  "DASHI/Physics/Closure/YMSprint110BottomSectorThresholdNoCollapse.agda"

weak110SourcePath : String
weak110SourcePath =
  "DASHI/Physics/Closure/YMSprint110WeakCompactnessEnergyCore.agda"

closed110SourcePath : String
closed110SourcePath =
  "DASHI/Physics/Closure/YMSprint110ClosedFormLowerSemicontinuityCriterion.agda"

recovery110SourcePath : String
recovery110SourcePath =
  "DASHI/Physics/Closure/YMSprint110RecoveryCoreDensityEnergyLimsup.agda"

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

reducerRecordedHere : Bool
reducerRecordedHere = true

packageAssembledHere : Bool
packageAssembledHere = true

rowsRecordedHere : Bool
rowsRecordedHere = true

weakCompactnessClosedHere : Bool
weakCompactnessClosedHere = false

closedFormLowerSemicontinuityClosedHere : Bool
closedFormLowerSemicontinuityClosedHere = false

recoveryLimsupClosedHere : Bool
recoveryLimsupClosedHere = false

moscoPackageClosedHere : Bool
moscoPackageClosedHere = false

h3aTraceNormResolventClosedHere : Bool
h3aTraceNormResolventClosedHere = false

h3bVacuumProjectionContinuityClosedHere : Bool
h3bVacuumProjectionContinuityClosedHere = false

noSpectralPollutionClosedHere : Bool
noSpectralPollutionClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromotedHere : Bool
clayYangMillsPromotedHere = false

reducerStatementText : String
reducerStatementText =
  "Sprint119 records the Mosco package as upstream compactness-and-form data only. Mosco yields common-domain control, liminf, recovery, and form-level convergence, but not positive-gap survival. H3a trace / norm-resolvent control and H3b vacuum-projection continuity are named separately, and no-spectral-pollution is downstream of those stronger obligations."

weakCompactnessResolutionText : String
weakCompactnessResolutionText =
  "Resolve weak compactness by extracting weakly convergent subsequences for bounded-energy finite transfer-form sequences on one physical carrier."

closedFormLowerSemicontinuityResolutionText : String
closedFormLowerSemicontinuityResolutionText =
  "Resolve the Mosco liminf side by identifying the common closed semibounded form domain and proving lower semicontinuity on weak bounded-energy limits."

recoveryLimsupResolutionText : String
recoveryLimsupResolutionText =
  "Resolve the Mosco recovery side by producing dense finite physical cores, compatible interpolation / sampling maps, strong norm recovery, and energy limsup."

moscoPackageResolutionText : String
moscoPackageResolutionText =
  "Assemble the Mosco package only after weak compactness, liminf, and recovery all close, together with the fail-closed recognition that this package gives form compactness and liminf control rather than continuum gap survival."

h3aTraceNormResolventResolutionText : String
h3aTraceNormResolventResolutionText =
  "Resolve H3a by proving trace / norm-resolvent control of the vacuum-orthogonal transfer sector. This is the load-bearing no-spectral-pollution obligation and is stronger than Mosco convergence alone."

h3bVacuumProjectionContinuityResolutionText : String
h3bVacuumProjectionContinuityResolutionText =
  "Resolve H3b by proving vacuum-projection continuity for the OS-compatible limiting vacuum, downstream of H3a plus the RP.4 reconstruction input."

noSpectralPollutionResolutionText : String
noSpectralPollutionResolutionText =
  "Resolve no-spectral-pollution only after H3a and H3b: use strong transfer control and vacuum-sector continuity to rule out spurious continuum eigenbranches below the finite lower threshold."

finalBoundaryText : String
finalBoundaryText =
  "The reducer now distinguishes Mosco compactness obligations from the stronger continuum-transfer obligations. Weak compactness, liminf, recovery, aggregate Mosco closure, H3a trace / norm-resolvent control, H3b vacuum-projection continuity, no-spectral-pollution, transfer readiness, transfer theorem, continuum mass gap, and Clay Yang-Mills promotion all remain false here."

data ObligationStage : Set where
  mosco-upstream-stage :
    ObligationStage
  h3a-transfer-stage :
    ObligationStage
  h3b-vacuum-stage :
    ObligationStage
  no-spectral-pollution-stage :
    ObligationStage
  final-boundary-stage :
    ObligationStage

data ReducerRowStatus : Set where
  imported-upstream-open :
    ReducerRowStatus
  mosco-package-only :
    ReducerRowStatus
  stronger-transfer-open :
    ReducerRowStatus
  downstream-open-after-h3a-h3b :
    ReducerRowStatus
  fail-closed-summary :
    ReducerRowStatus

data NormalizedMoscoObligation : Set where
  weak-compactness :
    NormalizedMoscoObligation
  closed-form-lower-semicontinuity :
    NormalizedMoscoObligation
  recovery-limsup :
    NormalizedMoscoObligation
  aggregate-mosco-package :
    NormalizedMoscoObligation
  h3a-trace-norm-resolvent-control :
    NormalizedMoscoObligation
  h3b-vacuum-projection-continuity :
    NormalizedMoscoObligation
  downstream-no-spectral-pollution :
    NormalizedMoscoObligation

record ImportedCanonicalReceipts : Setω where
  constructor mkImportedCanonicalReceipts
  field
    sprint118Receipt :
      Sprint118.YMSprint118MoscoCompactnessReadinessAggregatorReceipt
    mosco108Receipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    compact109Receipt :
      Compact109.YMSprint109NoBottomSpectrumPollutionCompactnessReceipt
    collapse110Receipt :
      Collapse110.YMSprint110BottomSectorThresholdNoCollapseReceipt
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    closed110Receipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    recovery110Receipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    receiptsImported :
      Bool
    sprint118AllClosedFlag :
      Bool
    sprint118AllClosedFlagIsFalse :
      sprint118AllClosedFlag ≡ false
    sprint118WeakCompactnessFlag :
      Bool
    sprint118WeakCompactnessFlagIsFalse :
      sprint118WeakCompactnessFlag ≡ false
    sprint118TransferReadyFlag :
      Bool
    sprint118TransferReadyFlagIsFalse :
      sprint118TransferReadyFlag ≡ false

record MoscoObligationRow : Set where
  constructor mkMoscoObligationRow
  field
    obligation :
      NormalizedMoscoObligation
    stage :
      ObligationStage
    sourcePath :
      String
    requiredResolution :
      String
    upstreamFlag :
      Bool
    upstreamFlagIsFalse :
      upstreamFlag ≡ false
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    rowStatus :
      ReducerRowStatus

record NormalizedMoscoObligationTable : Set where
  constructor mkNormalizedMoscoObligationTable
  field
    weakCompactnessRow :
      MoscoObligationRow
    closedFormLowerSemicontinuityRow :
      MoscoObligationRow
    recoveryLimsupRow :
      MoscoObligationRow
    moscoPackageRow :
      MoscoObligationRow
    h3aTraceNormResolventRow :
      MoscoObligationRow
    h3bVacuumProjectionContinuityRow :
      MoscoObligationRow
    noSpectralPollutionRow :
      MoscoObligationRow
    rows :
      List MoscoObligationRow
    rowCount :
      Nat
    rowsRecordedInTable :
      Bool
    packageAssembledInTable :
      Bool

record FinalMoscoReducerReceipt : Set where
  constructor mkFinalMoscoReducerReceipt
  field
    reducerRecordedFinal :
      Bool
    packageAssembledFinal :
      Bool
    rowsRecordedFinal :
      Bool
    moscoPackageClosedFinal :
      Bool
    moscoPackageClosedFinalIsFalse :
      moscoPackageClosedFinal ≡ false
    h3aTraceNormResolventClosedFinal :
      Bool
    h3aTraceNormResolventClosedFinalIsFalse :
      h3aTraceNormResolventClosedFinal ≡ false
    h3bVacuumProjectionContinuityClosedFinal :
      Bool
    h3bVacuumProjectionContinuityClosedFinalIsFalse :
      h3bVacuumProjectionContinuityClosedFinal ≡ false
    noSpectralPollutionClosedFinal :
      Bool
    noSpectralPollutionClosedFinalIsFalse :
      noSpectralPollutionClosedFinal ≡ false
    transferLowerBoundReadyFinal :
      Bool
    transferLowerBoundReadyFinalIsFalse :
      transferLowerBoundReadyFinal ≡ false
    transferLowerBoundTheoremProvedFinal :
      Bool
    transferLowerBoundTheoremProvedFinalIsFalse :
      transferLowerBoundTheoremProvedFinal ≡ false
    continuumMassGapProvedFinal :
      Bool
    continuumMassGapProvedFinalIsFalse :
      continuumMassGapProvedFinal ≡ false
    clayYangMillsPromotedFinal :
      Bool
    clayYangMillsPromotedFinalIsFalse :
      clayYangMillsPromotedFinal ≡ false
    finalStatement :
      String

record YMSprint119MoscoAllObligationsReducerReceipt : Setω where
  constructor mkYMSprint119MoscoAllObligationsReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedCanonicalReceipts :
      ImportedCanonicalReceipts
    normalizedObligationTable :
      NormalizedMoscoObligationTable
    finalReceipt :
      FinalMoscoReducerReceipt
    sourcePaths :
      List String
    requiredResolutions :
      List String
    rowStatuses :
      List ReducerRowStatus
    canonicalReceiptRecorded :
      Bool
    packageAssembledReceipt :
      Bool
    rowsRecordedReceipt :
      Bool
    moscoPackageClosedHereFlag :
      Bool
    moscoPackageClosedHereIsFalse :
      moscoPackageClosedHereFlag ≡ false
    h3aTraceNormResolventClosedHereFlag :
      Bool
    h3aTraceNormResolventClosedHereIsFalse :
      h3aTraceNormResolventClosedHereFlag ≡ false
    h3bVacuumProjectionContinuityClosedHereFlag :
      Bool
    h3bVacuumProjectionContinuityClosedHereIsFalse :
      h3bVacuumProjectionContinuityClosedHereFlag ≡ false
    noSpectralPollutionClosedHereFlag :
      Bool
    noSpectralPollutionClosedHereIsFalse :
      noSpectralPollutionClosedHereFlag ≡ false
    clayYangMillsPromotedHereFlag :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHereFlag ≡ false

open YMSprint119MoscoAllObligationsReducerReceipt public

canonicalImportedCanonicalReceipts : ImportedCanonicalReceipts
canonicalImportedCanonicalReceipts =
  mkImportedCanonicalReceipts
    Sprint118.canonicalReceipt
    Mosco108.canonicalReceipt
    Compact109.canonicalReceipt
    Collapse110.canonicalReceipt
    Weak110.canonicalReceipt
    Closed110.canonicalReceipt
    Recovery110.canonicalReceipt
    true
    Sprint118.allMoscoCompactnessObligationsClosedHere
    refl
    Sprint118.weakCompactnessClosedHere
    refl
    Sprint118.transferLowerBoundReadyHere
    refl

weakCompactnessRow : MoscoObligationRow
weakCompactnessRow =
  mkMoscoObligationRow
    weak-compactness
    mosco-upstream-stage
    weak110SourcePath
    weakCompactnessResolutionText
    Weak110.weakSubsequenceExtractionProvedHere
    refl
    weakCompactnessClosedHere
    refl
    imported-upstream-open

closedFormLowerSemicontinuityRow : MoscoObligationRow
closedFormLowerSemicontinuityRow =
  mkMoscoObligationRow
    closed-form-lower-semicontinuity
    mosco-upstream-stage
    closed110SourcePath
    closedFormLowerSemicontinuityResolutionText
    Closed110.closedFormCriterionClosedHere
    refl
    closedFormLowerSemicontinuityClosedHere
    refl
    imported-upstream-open

recoveryLimsupRow : MoscoObligationRow
recoveryLimsupRow =
  mkMoscoObligationRow
    recovery-limsup
    mosco-upstream-stage
    recovery110SourcePath
    recoveryLimsupResolutionText
    Recovery110.moscoRecoverySideClosedHere
    refl
    recoveryLimsupClosedHere
    refl
    imported-upstream-open

moscoPackageRow : MoscoObligationRow
moscoPackageRow =
  mkMoscoObligationRow
    aggregate-mosco-package
    mosco-upstream-stage
    sprint118SourcePath
    moscoPackageResolutionText
    Sprint118.allMoscoCompactnessObligationsClosedHere
    refl
    moscoPackageClosedHere
    refl
    mosco-package-only

h3aTraceNormResolventRow : MoscoObligationRow
h3aTraceNormResolventRow =
  mkMoscoObligationRow
    h3a-trace-norm-resolvent-control
    h3a-transfer-stage
    mosco108SourcePath
    h3aTraceNormResolventResolutionText
    Mosco108.canonicalReceiptTargetTheoremProvedHere
    refl
    h3aTraceNormResolventClosedHere
    refl
    stronger-transfer-open

h3bVacuumProjectionContinuityRow : MoscoObligationRow
h3bVacuumProjectionContinuityRow =
  mkMoscoObligationRow
    h3b-vacuum-projection-continuity
    h3b-vacuum-stage
    compact109SourcePath
    h3bVacuumProjectionContinuityResolutionText
    Compact109.noBottomSpectrumPollutionCompactnessTheoremProved
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    stronger-transfer-open

noSpectralPollutionRow : MoscoObligationRow
noSpectralPollutionRow =
  mkMoscoObligationRow
    downstream-no-spectral-pollution
    no-spectral-pollution-stage
    collapse110SourcePath
    noSpectralPollutionResolutionText
    Collapse110.noCollapseAtZeroClosed
    refl
    noSpectralPollutionClosedHere
    refl
    downstream-open-after-h3a-h3b

canonicalRows : List MoscoObligationRow
canonicalRows =
  weakCompactnessRow
  ∷ closedFormLowerSemicontinuityRow
  ∷ recoveryLimsupRow
  ∷ moscoPackageRow
  ∷ h3aTraceNormResolventRow
  ∷ h3bVacuumProjectionContinuityRow
  ∷ noSpectralPollutionRow
  ∷ []

canonicalNormalizedMoscoObligationTable : NormalizedMoscoObligationTable
canonicalNormalizedMoscoObligationTable =
  mkNormalizedMoscoObligationTable
    weakCompactnessRow
    closedFormLowerSemicontinuityRow
    recoveryLimsupRow
    moscoPackageRow
    h3aTraceNormResolventRow
    h3bVacuumProjectionContinuityRow
    noSpectralPollutionRow
    canonicalRows
    7
    rowsRecordedHere
    packageAssembledHere

canonicalFinalMoscoReducerReceipt : FinalMoscoReducerReceipt
canonicalFinalMoscoReducerReceipt =
  mkFinalMoscoReducerReceipt
    reducerRecordedHere
    packageAssembledHere
    rowsRecordedHere
    moscoPackageClosedHere
    refl
    h3aTraceNormResolventClosedHere
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromotedHere
    refl
    finalBoundaryText

canonicalSourcePaths : List String
canonicalSourcePaths =
  modulePath
  ∷ sprint118SourcePath
  ∷ mosco108SourcePath
  ∷ compact109SourcePath
  ∷ collapse110SourcePath
  ∷ weak110SourcePath
  ∷ closed110SourcePath
  ∷ recovery110SourcePath
  ∷ []

canonicalRequiredResolutions : List String
canonicalRequiredResolutions =
  weakCompactnessResolutionText
  ∷ closedFormLowerSemicontinuityResolutionText
  ∷ recoveryLimsupResolutionText
  ∷ moscoPackageResolutionText
  ∷ h3aTraceNormResolventResolutionText
  ∷ h3bVacuumProjectionContinuityResolutionText
  ∷ noSpectralPollutionResolutionText
  ∷ []

canonicalRowStatuses : List ReducerRowStatus
canonicalRowStatuses =
  imported-upstream-open
  ∷ imported-upstream-open
  ∷ imported-upstream-open
  ∷ mosco-package-only
  ∷ stronger-transfer-open
  ∷ stronger-transfer-open
  ∷ downstream-open-after-h3a-h3b
  ∷ fail-closed-summary
  ∷ []

canonicalYMSprint119MoscoAllObligationsReducerReceipt :
  YMSprint119MoscoAllObligationsReducerReceipt
canonicalYMSprint119MoscoAllObligationsReducerReceipt =
  mkYMSprint119MoscoAllObligationsReducerReceipt
    sprintNumber
    modulePath
    canonicalImportedCanonicalReceipts
    canonicalNormalizedMoscoObligationTable
    canonicalFinalMoscoReducerReceipt
    canonicalSourcePaths
    canonicalRequiredResolutions
    canonicalRowStatuses
    reducerRecordedHere
    packageAssembledHere
    rowsRecordedHere
    moscoPackageClosedHere
    refl
    h3aTraceNormResolventClosedHere
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionClosedHere
    refl
    clayYangMillsPromotedHere
    refl

canonicalReceipt :
  YMSprint119MoscoAllObligationsReducerReceipt
canonicalReceipt =
  canonicalYMSprint119MoscoAllObligationsReducerReceipt

finalReceiptAlias :
  YMSprint119MoscoAllObligationsReducerReceipt
finalReceiptAlias =
  canonicalReceipt

canonicalReceiptMoscoPackageClosedHereIsFalse :
  moscoPackageClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptMoscoPackageClosedHereIsFalse =
  refl

canonicalReceiptH3aTraceNormResolventClosedHereIsFalse :
  h3aTraceNormResolventClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptH3aTraceNormResolventClosedHereIsFalse =
  refl

canonicalReceiptH3bVacuumProjectionContinuityClosedHereIsFalse :
  h3bVacuumProjectionContinuityClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptH3bVacuumProjectionContinuityClosedHereIsFalse =
  refl

canonicalReceiptNoSpectralPollutionClosedHereIsFalse :
  noSpectralPollutionClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptNoSpectralPollutionClosedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedHereIsFalse :
  clayYangMillsPromotedHereFlag canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedHereIsFalse =
  refl
