module DASHI.Physics.Closure.YMSprint124MoscoRecoveryNoPollutionInterface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint109MoscoLiminfLowerSemicontinuity
  as MC1
import DASHI.Physics.Closure.YMSprint123WeakCompactnessExtractionInterface
  as WC1
import DASHI.Physics.Closure.YMSprint123UniformFormLowerBoundInterface
  as MC3

------------------------------------------------------------------------
-- Sprint124 MC2/MC4 Mosco recovery and no-pollution interface.
--
-- This module is an inhabited fail-closed ledger.  It records the MC2
-- Mosco recovery-limsup route and the MC4 no bottom-spectrum pollution
-- route over MC1, WC1, and MC3.  It proves no analytic recovery theorem, no
-- no-pollution theorem, no Mosco compactness closure, no transfer theorem,
-- no continuum mass gap, and no Clay Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 124

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint124MoscoRecoveryNoPollutionInterface.agda"

interfaceName : String
interfaceName =
  "Sprint124 MC2 recovery limsup and MC4 no bottom spectrum pollution interface"

mc2LaneName : String
mc2LaneName = "MC2-Mosco-recovery-limsup"

mc4LaneName : String
mc4LaneName = "MC4-no-bottom-spectrum-pollution"

mc1SourcePath : String
mc1SourcePath =
  "DASHI/Physics/Closure/YMSprint109MoscoLiminfLowerSemicontinuity.agda"

wc1SourcePath : String
wc1SourcePath = WC1.modulePath

mc3SourcePath : String
mc3SourcePath = MC3.modulePath

interfaceRecorded : Bool
interfaceRecorded = true

mc2RecoveryRouteRecorded : Bool
mc2RecoveryRouteRecorded = true

mc4NoPollutionRouteRecorded : Bool
mc4NoPollutionRouteRecorded = true

dependencyRowsRecorded : Bool
dependencyRowsRecorded = true

blockersRecorded : Bool
blockersRecorded = true

falseTheoremAndPromotionFlagsRecorded : Bool
falseTheoremAndPromotionFlagsRecorded = true

mc1ClosedInput : Bool
mc1ClosedInput = MC1.transferLiminfLowerBoundPathClosedHere

wc1ClosedInput : Bool
wc1ClosedInput = WC1.weakCompactnessClosedHere

mc3ClosedInput : Bool
mc3ClosedInput = MC3.mc3UniformFormLowerBoundProvedHere

mc1ClosedInputIsFalse : mc1ClosedInput ≡ false
mc1ClosedInputIsFalse = refl

wc1ClosedInputIsFalse : wc1ClosedInput ≡ false
wc1ClosedInputIsFalse = refl

mc3ClosedInputIsFalse : mc3ClosedInput ≡ false
mc3ClosedInputIsFalse = refl

mc2RecoveryLimsupProvedHere : Bool
mc2RecoveryLimsupProvedHere = false

mc2RecoveryLimsupClaimedHere : Bool
mc2RecoveryLimsupClaimedHere = false

mc4NoBottomSpectrumPollutionProvedHere : Bool
mc4NoBottomSpectrumPollutionProvedHere = false

mc4NoBottomSpectrumPollutionClaimedHere : Bool
mc4NoBottomSpectrumPollutionClaimedHere = false

moscoRecoverySequenceTheoremProvedHere : Bool
moscoRecoverySequenceTheoremProvedHere = false

bottomSpectrumCompactnessTheoremProvedHere : Bool
bottomSpectrumCompactnessTheoremProvedHere = false

spuriousBottomBranchExclusionProvedHere : Bool
spuriousBottomBranchExclusionProvedHere = false

allMoscoCompactnessObligationsClosedHere : Bool
allMoscoCompactnessObligationsClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

mc2StatementText : String
mc2StatementText =
  "MC2 route: for every continuum physical form-domain vector, build finite physical approximants on the common carrier with strong recovery and finite-transfer energy limsup control."

mc4StatementText : String
mc4StatementText =
  "MC4 route: rule out spurious finite bottom-spectrum branches by combining WC1 compact extraction, MC1 liminf control, and MC3 uniform lower bounds on the physical non-vacuum sector."

dependencyStatementText : String
dependencyStatementText =
  "Dependencies: MC2 and MC4 consume MC1 liminf lower semicontinuity, WC1 weak compactness extraction, and MC3 uniform form lower bound; all imported theorem flags are false."

blockerStatementText : String
blockerStatementText =
  "Blockers: MC1 path closure, WC1 weak compactness, and MC3 lower-bound theorem remain open, so recovery limsup and no-bottom-pollution stay ledger-only."

falseFlagStatementText : String
falseFlagStatementText =
  "False flags: no MC2 proof, no MC4 proof, no Mosco closure, no transfer lower-bound theorem, no continuum mass gap, and no Clay Yang-Mills promotion is asserted here."

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical Sprint124 receipt: MC2 recovery-limsup and MC4 no-bottom-spectrum-pollution interfaces are inhabited as fail-closed ledgers over MC1, WC1, and MC3 with blockers and false theorem flags proved."

data Sprint124Lane : Set where
  mc1-liminf-dependency-lane :
    Sprint124Lane
  wc1-weak-compactness-dependency-lane :
    Sprint124Lane
  mc3-form-lower-bound-dependency-lane :
    Sprint124Lane
  mc2-recovery-limsup-lane :
    Sprint124Lane
  mc4-no-bottom-pollution-lane :
    Sprint124Lane
  blocker-ledger-lane :
    Sprint124Lane
  false-theorem-promotion-flag-lane :
    Sprint124Lane

data RouteStatus : Set where
  dependency-imported :
    RouteStatus
  route-piece-recorded :
    RouteStatus
  analytic-input-required :
    RouteStatus
  blocked-by-open-upstream :
    RouteStatus
  theorem-flag-false :
    RouteStatus
  nonpromotion-recorded :
    RouteStatus
  canonical-receipt-inhabited :
    RouteStatus

data MC2RouteKind : Set where
  dense-core-selection :
    MC2RouteKind
  finite-approximant-construction :
    MC2RouteKind
  strong-carrier-recovery :
    MC2RouteKind
  gauge-quotient-descent :
    MC2RouteKind
  energy-limsup-control :
    MC2RouteKind

data MC4RouteKind : Set where
  low-energy-branch-selection :
    MC4RouteKind
  wc1-compact-extraction :
    MC4RouteKind
  mc1-liminf-comparison :
    MC4RouteKind
  mc3-uniform-lower-bound :
    MC4RouteKind
  spurious-bottom-branch-exclusion :
    MC4RouteKind

canonicalLanes : List Sprint124Lane
canonicalLanes =
  mc1-liminf-dependency-lane
  ∷ wc1-weak-compactness-dependency-lane
  ∷ mc3-form-lower-bound-dependency-lane
  ∷ mc2-recovery-limsup-lane
  ∷ mc4-no-bottom-pollution-lane
  ∷ blocker-ledger-lane
  ∷ false-theorem-promotion-flag-lane
  ∷ []

record UpstreamDependency : Setω where
  constructor mkUpstreamDependency
  field
    dependencyName :
      String
    dependencyPath :
      String
    requiredForMC2 :
      Bool
    requiredForMC2IsTrue :
      requiredForMC2 ≡ true
    requiredForMC4 :
      Bool
    requiredForMC4IsTrue :
      requiredForMC4 ≡ true
    closedInput :
      Bool
    closedInputIsFalse :
      closedInput ≡ false
    status :
      RouteStatus
    statement :
      String

record UpstreamReceipts : Setω where
  constructor mkUpstreamReceipts
  field
    mc1Receipt :
      MC1.YMSprint109MoscoLiminfLowerSemicontinuityReceipt
    wc1Receipt :
      WC1.YMSprint123WeakCompactnessExtractionInterfaceReceipt
    mc3Receipt :
      MC3.YMSprint123UniformFormLowerBoundInterfaceReceipt
    mc1Dependency :
      UpstreamDependency
    wc1Dependency :
      UpstreamDependency
    mc3Dependency :
      UpstreamDependency
    dependenciesRecorded :
      Bool
    dependenciesRecordedIsTrue :
      dependenciesRecorded ≡ true
    statement :
      String

record MC2RoutePiece : Set where
  constructor mkMC2RoutePiece
  field
    kind :
      MC2RouteKind
    routeName :
      String
    requiredInput :
      String
    blocker :
      String
    recorded :
      Bool
    recordedIsTrue :
      recorded ≡ true
    theoremAvailableHere :
      Bool
    theoremAvailableHereIsFalse :
      theoremAvailableHere ≡ false
    status :
      RouteStatus

record MC2RecoveryLimsupLedger : Set where
  constructor mkMC2RecoveryLimsupLedger
  field
    denseCore :
      MC2RoutePiece
    finiteApproximants :
      MC2RoutePiece
    strongRecovery :
      MC2RoutePiece
    quotientDescent :
      MC2RoutePiece
    energyLimsup :
      MC2RoutePiece
    routeRecorded :
      Bool
    routeRecordedIsTrue :
      routeRecorded ≡ true
    mc2Proved :
      Bool
    mc2ProvedIsFalse :
      mc2Proved ≡ false
    statement :
      String

record MC4RoutePiece : Set where
  constructor mkMC4RoutePiece
  field
    kind :
      MC4RouteKind
    routeName :
      String
    requiredInput :
      String
    pollutionRisk :
      String
    guard :
      String
    recorded :
      Bool
    recordedIsTrue :
      recorded ≡ true
    proofAvailableHere :
      Bool
    proofAvailableHereIsFalse :
      proofAvailableHere ≡ false
    status :
      RouteStatus

record MC4NoBottomPollutionLedger : Set where
  constructor mkMC4NoBottomPollutionLedger
  field
    branchSelection :
      MC4RoutePiece
    compactExtraction :
      MC4RoutePiece
    liminfComparison :
      MC4RoutePiece
    lowerBoundGuard :
      MC4RoutePiece
    branchExclusion :
      MC4RoutePiece
    routeRecorded :
      Bool
    routeRecordedIsTrue :
      routeRecorded ≡ true
    mc4Proved :
      Bool
    mc4ProvedIsFalse :
      mc4Proved ≡ false
    statement :
      String

record BlockerRow : Set where
  constructor mkBlockerRow
  field
    blockerName :
      String
    sourcePath :
      String
    currentFlag :
      Bool
    currentFlagIsFalse :
      currentFlag ≡ false
    blocksMC2 :
      Bool
    blocksMC2IsTrue :
      blocksMC2 ≡ true
    blocksMC4 :
      Bool
    blocksMC4IsTrue :
      blocksMC4 ≡ true
    promotionAllowed :
      Bool
    promotionAllowedIsFalse :
      promotionAllowed ≡ false
    status :
      RouteStatus

record BlockerLedger : Set where
  constructor mkBlockerLedger
  field
    mc1Blocker :
      BlockerRow
    wc1Blocker :
      BlockerRow
    mc3Blocker :
      BlockerRow
    blockersRecordedFlag :
      Bool
    blockersRecordedFlagIsTrue :
      blockersRecordedFlag ≡ true
    statement :
      String

record FalseTheoremAndPromotionFlags : Set where
  constructor mkFalseTheoremAndPromotionFlags
  field
    mc2Proved :
      Bool
    mc2ProvedIsFalse :
      mc2Proved ≡ false
    mc2Claimed :
      Bool
    mc2ClaimedIsFalse :
      mc2Claimed ≡ false
    mc4Proved :
      Bool
    mc4ProvedIsFalse :
      mc4Proved ≡ false
    mc4Claimed :
      Bool
    mc4ClaimedIsFalse :
      mc4Claimed ≡ false
    recoverySequenceTheoremProved :
      Bool
    recoverySequenceTheoremProvedIsFalse :
      recoverySequenceTheoremProved ≡ false
    bottomSpectrumCompactnessTheoremProved :
      Bool
    bottomSpectrumCompactnessTheoremProvedIsFalse :
      bottomSpectrumCompactnessTheoremProved ≡ false
    spuriousBottomBranchExclusionProved :
      Bool
    spuriousBottomBranchExclusionProvedIsFalse :
      spuriousBottomBranchExclusionProved ≡ false
    allMoscoCompactnessObligationsClosed :
      Bool
    allMoscoCompactnessObligationsClosedIsFalse :
      allMoscoCompactnessObligationsClosed ≡ false
    transferLowerBoundReady :
      Bool
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundTheoremProved :
      Bool
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProved ≡ false
    continuumMassGapProved :
      Bool
    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    flagsRecorded :
      Bool
    flagsRecordedIsTrue :
      flagsRecorded ≡ true
    statement :
      String

record YMSprint124MoscoRecoveryNoPollutionInterfaceReceipt : Setω where
  constructor mkYMSprint124MoscoRecoveryNoPollutionInterfaceReceipt
  field
    laneMC2 :
      String
    laneMC4 :
      String
    currentModulePath :
      String
    upstreamReceipts :
      UpstreamReceipts
    mc2RecoveryLedger :
      MC2RecoveryLimsupLedger
    mc4NoPollutionLedger :
      MC4NoBottomPollutionLedger
    blockerLedger :
      BlockerLedger
    falseTheoremAndPromotionFlags :
      FalseTheoremAndPromotionFlags
    lanes :
      List Sprint124Lane
    interfaceRecordedFlag :
      Bool
    interfaceRecordedFlagIsTrue :
      interfaceRecordedFlag ≡ true
    mc2RouteRecordedFlag :
      Bool
    mc2RouteRecordedFlagIsTrue :
      mc2RouteRecordedFlag ≡ true
    mc4RouteRecordedFlag :
      Bool
    mc4RouteRecordedFlagIsTrue :
      mc4RouteRecordedFlag ≡ true
    dependenciesRecordedFlag :
      Bool
    dependenciesRecordedFlagIsTrue :
      dependenciesRecordedFlag ≡ true
    blockersRecordedFlag :
      Bool
    blockersRecordedFlagIsTrue :
      blockersRecordedFlag ≡ true
    mc2Closed :
      Bool
    mc2ClosedIsFalse :
      mc2Closed ≡ false
    mc4Closed :
      Bool
    mc4ClosedIsFalse :
      mc4Closed ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    statement :
      String

canonicalUpstreamReceipts : UpstreamReceipts
canonicalUpstreamReceipts =
  mkUpstreamReceipts
    MC1.canonicalReceipt
    WC1.canonicalYMSprint123WeakCompactnessExtractionInterfaceReceipt
    MC3.canonicalReceipt
    (mkUpstreamDependency
      "MC1 Mosco liminf lower semicontinuity"
      mc1SourcePath
      true refl
      true refl
      mc1ClosedInput refl
      blocked-by-open-upstream
      "MC1 supplies liminf comparison, but its transfer liminf path is false.")
    (mkUpstreamDependency
      "WC1 weak compactness extraction"
      wc1SourcePath
      true refl
      true refl
      wc1ClosedInput refl
      blocked-by-open-upstream
      "WC1 supplies compact extraction for low-energy branches, but weak compactness is false.")
    (mkUpstreamDependency
      "MC3 uniform form lower bound"
      mc3SourcePath
      true refl
      true refl
      mc3ClosedInput refl
      blocked-by-open-upstream
      "MC3 supplies lower-bound constants and windows, but its theorem flag is false.")
    true
    refl
    dependencyStatementText

canonicalMC2RecoveryLimsupLedger : MC2RecoveryLimsupLedger
canonicalMC2RecoveryLimsupLedger =
  mkMC2RecoveryLimsupLedger
    (mkMC2RoutePiece
      dense-core-selection
      "dense physical core selection"
      "common continuum form-domain core shared by MC1 and MC3"
      "no closed density theorem on the Sprint124 carrier is proved"
      true refl false refl route-piece-recorded)
    (mkMC2RoutePiece
      finite-approximant-construction
      "finite physical approximant construction"
      "renormalized finite carrier maps compatible with the quotient"
      "approximants are specified as required route pieces only"
      true refl false refl route-piece-recorded)
    (mkMC2RoutePiece
      strong-carrier-recovery
      "strong common-carrier recovery"
      "MC3 norm window and MC1 carrier identification"
      "strong recovery is not derived from the imported ledgers"
      true refl false refl analytic-input-required)
    (mkMC2RoutePiece
      gauge-quotient-descent
      "gauge quotient descent"
      "representative-independent finite approximants"
      "quotient descent remains a compatibility obligation"
      true refl false refl analytic-input-required)
    (mkMC2RoutePiece
      energy-limsup-control
      "finite energy limsup control"
      "MC3 uniform lower-bound window and MC1 lower-semicontinuity lane"
      "energy limsup inequality is not proved here"
      true refl false refl theorem-flag-false)
    true
    refl
    false
    refl
    mc2StatementText

canonicalMC4NoBottomPollutionLedger : MC4NoBottomPollutionLedger
canonicalMC4NoBottomPollutionLedger =
  mkMC4NoBottomPollutionLedger
    (mkMC4RoutePiece
      low-energy-branch-selection
      "low-energy bottom branch selection"
      "normalized non-vacuum finite branch near the lower spectral edge"
      "spurious bottom branch may be selected without compactness"
      "record branch and require compact extraction before promotion"
      true refl false refl route-piece-recorded)
    (mkMC4RoutePiece
      wc1-compact-extraction
      "WC1 compact extraction"
      "Sprint123 WC1 weak compactness extraction interface"
      "branch can escape the common physical carrier"
      "consume WC1 only after weakCompactnessClosedHere=true"
      true refl false refl blocked-by-open-upstream)
    (mkMC4RoutePiece
      mc1-liminf-comparison
      "MC1 liminf comparison"
      "Sprint109 MC1 liminf lower-semicontinuity ledger"
      "finite lower edge can fall below the continuum lower edge"
      "consume MC1 only after the transfer liminf path closes"
      true refl false refl blocked-by-open-upstream)
    (mkMC4RoutePiece
      mc3-uniform-lower-bound
      "MC3 uniform lower-bound guard"
      "Sprint123 MC3 uniform form lower-bound interface"
      "finite branch can evade the non-vacuum lower-bound window"
      "consume MC3 only after the lower-bound theorem closes"
      true refl false refl blocked-by-open-upstream)
    (mkMC4RoutePiece
      spurious-bottom-branch-exclusion
      "spurious bottom branch exclusion"
      "combined MC1/WC1/MC3 closed package"
      "false finite branch could pollute the continuum bottom spectrum"
      "require all upstream gates before no-pollution promotion"
      true refl false refl theorem-flag-false)
    true
    refl
    false
    refl
    mc4StatementText

canonicalBlockerLedger : BlockerLedger
canonicalBlockerLedger =
  mkBlockerLedger
    (mkBlockerRow
      "MC1 liminf path open"
      mc1SourcePath
      mc1ClosedInput refl
      true refl
      true refl
      false refl
      blocked-by-open-upstream)
    (mkBlockerRow
      "WC1 weak compactness open"
      wc1SourcePath
      wc1ClosedInput refl
      true refl
      true refl
      false refl
      blocked-by-open-upstream)
    (mkBlockerRow
      "MC3 uniform form theorem open"
      mc3SourcePath
      mc3ClosedInput refl
      true refl
      true refl
      false refl
      blocked-by-open-upstream)
    true
    refl
    blockerStatementText

canonicalFalseTheoremAndPromotionFlags :
  FalseTheoremAndPromotionFlags
canonicalFalseTheoremAndPromotionFlags =
  mkFalseTheoremAndPromotionFlags
    mc2RecoveryLimsupProvedHere refl
    mc2RecoveryLimsupClaimedHere refl
    mc4NoBottomSpectrumPollutionProvedHere refl
    mc4NoBottomSpectrumPollutionClaimedHere refl
    moscoRecoverySequenceTheoremProvedHere refl
    bottomSpectrumCompactnessTheoremProvedHere refl
    spuriousBottomBranchExclusionProvedHere refl
    allMoscoCompactnessObligationsClosedHere refl
    transferLowerBoundReadyHere refl
    transferLowerBoundTheoremProvedHere refl
    continuumMassGapProvedHere refl
    clayYangMillsPromoted refl
    true refl
    falseFlagStatementText

canonicalYMSprint124MoscoRecoveryNoPollutionInterfaceReceipt :
  YMSprint124MoscoRecoveryNoPollutionInterfaceReceipt
canonicalYMSprint124MoscoRecoveryNoPollutionInterfaceReceipt =
  mkYMSprint124MoscoRecoveryNoPollutionInterfaceReceipt
    mc2LaneName
    mc4LaneName
    modulePath
    canonicalUpstreamReceipts
    canonicalMC2RecoveryLimsupLedger
    canonicalMC4NoBottomPollutionLedger
    canonicalBlockerLedger
    canonicalFalseTheoremAndPromotionFlags
    canonicalLanes
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    canonicalReceiptText

canonicalReceipt :
  YMSprint124MoscoRecoveryNoPollutionInterfaceReceipt
canonicalReceipt =
  canonicalYMSprint124MoscoRecoveryNoPollutionInterfaceReceipt

finalReceipt :
  YMSprint124MoscoRecoveryNoPollutionInterfaceReceipt
finalReceipt =
  canonicalReceipt

interfaceRecordedIsTrue : interfaceRecorded ≡ true
interfaceRecordedIsTrue = refl

mc2RecoveryRouteRecordedIsTrue : mc2RecoveryRouteRecorded ≡ true
mc2RecoveryRouteRecordedIsTrue = refl

mc4NoPollutionRouteRecordedIsTrue :
  mc4NoPollutionRouteRecorded ≡ true
mc4NoPollutionRouteRecordedIsTrue = refl

dependencyRowsRecordedIsTrue : dependencyRowsRecorded ≡ true
dependencyRowsRecordedIsTrue = refl

blockersRecordedIsTrue : blockersRecorded ≡ true
blockersRecordedIsTrue = refl

falseTheoremAndPromotionFlagsRecordedIsTrue :
  falseTheoremAndPromotionFlagsRecorded ≡ true
falseTheoremAndPromotionFlagsRecordedIsTrue = refl

mc2RecoveryLimsupProvedHereIsFalse :
  mc2RecoveryLimsupProvedHere ≡ false
mc2RecoveryLimsupProvedHereIsFalse = refl

mc2RecoveryLimsupClaimedHereIsFalse :
  mc2RecoveryLimsupClaimedHere ≡ false
mc2RecoveryLimsupClaimedHereIsFalse = refl

mc4NoBottomSpectrumPollutionProvedHereIsFalse :
  mc4NoBottomSpectrumPollutionProvedHere ≡ false
mc4NoBottomSpectrumPollutionProvedHereIsFalse = refl

mc4NoBottomSpectrumPollutionClaimedHereIsFalse :
  mc4NoBottomSpectrumPollutionClaimedHere ≡ false
mc4NoBottomSpectrumPollutionClaimedHereIsFalse = refl

moscoRecoverySequenceTheoremProvedHereIsFalse :
  moscoRecoverySequenceTheoremProvedHere ≡ false
moscoRecoverySequenceTheoremProvedHereIsFalse = refl

bottomSpectrumCompactnessTheoremProvedHereIsFalse :
  bottomSpectrumCompactnessTheoremProvedHere ≡ false
bottomSpectrumCompactnessTheoremProvedHereIsFalse = refl

spuriousBottomBranchExclusionProvedHereIsFalse :
  spuriousBottomBranchExclusionProvedHere ≡ false
spuriousBottomBranchExclusionProvedHereIsFalse = refl

allMoscoCompactnessObligationsClosedHereIsFalse :
  allMoscoCompactnessObligationsClosedHere ≡ false
allMoscoCompactnessObligationsClosedHereIsFalse = refl

transferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHere ≡ false
transferLowerBoundReadyHereIsFalse = refl

transferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHere ≡ false
transferLowerBoundTheoremProvedHereIsFalse = refl

continuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHere ≡ false
continuumMassGapProvedHereIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl
