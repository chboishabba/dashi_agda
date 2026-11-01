module DASHI.Physics.Closure.YMSprint116NormGaugeWindowClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint113GaugeCovarianceLocalSectionEstimate
  as Gauge113
import DASHI.Physics.Closure.YMSprint113LocalJacobianPartitionEstimate
  as Local113
import DASHI.Physics.Closure.YMSprint113QuotientNormComparisonEstimate
  as Quot113
import DASHI.Physics.Closure.YMSprint114GaugeQuotientClosureCriterion
  as Gauge114
import DASHI.Physics.Closure.YMSprint114UniformNormConstantAssembly
  as Uniform114
import DASHI.Physics.Closure.YMSprint115NormWindowClosureCriterion
  as Norm115

------------------------------------------------------------------------
-- Sprint116 norm/gauge-window reducer.
--
-- This module is a closed reduction layer over Sprint115.  It packages
-- supplied analytic feeds, quotient/gauge feeds, and the C_package=645120
-- compatibility surface, then rebuilds the Sprint115 norm-window criterion
-- from those feeds.  Unconditional analytic closure remains fail-closed.

sprintNumber : Nat
sprintNumber = 116

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint116NormGaugeWindowClosureReducer.agda"

sprint115SourcePath : String
sprint115SourcePath =
  "DASHI/Physics/Closure/YMSprint115NormWindowClosureCriterion.agda"

uniform114SourcePath : String
uniform114SourcePath =
  "DASHI/Physics/Closure/YMSprint114UniformNormConstantAssembly.agda"

gauge114SourcePath : String
gauge114SourcePath =
  "DASHI/Physics/Closure/YMSprint114GaugeQuotientClosureCriterion.agda"

local113SourcePath : String
local113SourcePath =
  "DASHI/Physics/Closure/YMSprint113LocalJacobianPartitionEstimate.agda"

quotient113SourcePath : String
quotient113SourcePath =
  "DASHI/Physics/Closure/YMSprint113QuotientNormComparisonEstimate.agda"

gauge113SourcePath : String
gauge113SourcePath =
  "DASHI/Physics/Closure/YMSprint113GaugeCovarianceLocalSectionEstimate.agda"

normGaugeWindowReducerRecorded : Bool
normGaugeWindowReducerRecorded = true

normCriterionClosedHere : Bool
normCriterionClosedHere = true

externalNormWindowClosedHere : Bool
externalNormWindowClosedHere = false

unconditionalNormWindowTheoremProvedHere : Bool
unconditionalNormWindowTheoremProvedHere = false

quotientGaugeAnalyticFeedsDischargedHere : Bool
quotientGaugeAnalyticFeedsDischargedHere = false

externalAnalyticClosurePromotedHere : Bool
externalAnalyticClosurePromotedHere = false

terminalClayClaimPromoted : Bool
terminalClayClaimPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

reducerStatementText : String
reducerStatementText =
  "Sprint116 reducer: supplied Sprint115 norm-window analytic feeds, supplied Sprint114 quotient/gauge feeds, and C_package=645120 close the internal norm-window criterion conditionally."

normAnalyticFeedText : String
normAnalyticFeedText =
  "Norm-window analytic feed is inhabited by upper and lower supplied estimate fields, admissible a-window data, and Sprint115 supplied-field packaging."

quotientGaugeAnalyticFeedText : String
quotientGaugeAnalyticFeedText =
  "Quotient/gauge analytic feed is inhabited by the Sprint114 gauge-quotient closure inputs and criterion while its analytic discharge flag remains false."

packageConstantCompatibilityText : String
packageConstantCompatibilityText =
  "Package constant compatibility records 16 * 32 * 12 * 15 * 7 = 645120 and agrees with Sprint114 and Sprint115 package constants."

blockedAnalyticClosureText : String
blockedAnalyticClosureText =
  "Unconditional norm-window and quotient/gauge analytic closure are not proved here; the reducer records those flags as false and keeps promotion false."

data ReducerLane : Set where
  sprint115-norm-window-lane :
    ReducerLane
  sprint114-uniform-package-lane :
    ReducerLane
  sprint114-gauge-quotient-lane :
    ReducerLane
  sprint113-local-estimate-lane :
    ReducerLane
  sprint113-quotient-estimate-lane :
    ReducerLane
  sprint113-gauge-estimate-lane :
    ReducerLane
  package-constant-compatibility-lane :
    ReducerLane
  conditional-reducer-lane :
    ReducerLane
  blocked-analytic-closure-lane :
    ReducerLane
  receipt-lane :
    ReducerLane

data ReducerStatus : Set where
  imported-sprint115-criterion :
    ReducerStatus
  imported-sprint114-uniform :
    ReducerStatus
  imported-sprint114-gauge :
    ReducerStatus
  imported-sprint113-estimate :
    ReducerStatus
  feed-inhabited :
    ReducerStatus
  constant-compatible :
    ReducerStatus
  conditionally-closed :
    ReducerStatus
  blocked-false :
    ReducerStatus
  nonpromotion-false :
    ReducerStatus

canonicalReducerLanes : List ReducerLane
canonicalReducerLanes =
  sprint115-norm-window-lane
  ∷ sprint114-uniform-package-lane
  ∷ sprint114-gauge-quotient-lane
  ∷ sprint113-local-estimate-lane
  ∷ sprint113-quotient-estimate-lane
  ∷ sprint113-gauge-estimate-lane
  ∷ package-constant-compatibility-lane
  ∷ conditional-reducer-lane
  ∷ blocked-analytic-closure-lane
  ∷ receipt-lane
  ∷ []

record NormWindowAnalyticFeed : Setω where
  constructor mkNormWindowAnalyticFeed
  field
    suppliedFields :
      Norm115.SuppliedNormWindowFields
    sprint115Criterion :
      Norm115.NormWindowClosureCriterion
    upperFeedClosedInternally :
      Bool
    upperFeedClosedInternallyIsTrue :
      upperFeedClosedInternally ≡ true
    lowerFeedClosedInternally :
      Bool
    lowerFeedClosedInternallyIsTrue :
      lowerFeedClosedInternally ≡ true
    admissibleWindowRecorded :
      Bool
    admissibleWindowRecordedIsTrue :
      admissibleWindowRecorded ≡ true
    criterionFromFeedClosed :
      Bool
    criterionFromFeedClosedIsTrue :
      criterionFromFeedClosed ≡ true
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    statement :
      String
    status :
      ReducerStatus

normWindowAnalyticFeedFromSupplies :
  Norm115.SuppliedNormWindowFields →
  NormWindowAnalyticFeed
normWindowAnalyticFeedFromSupplies fields =
  mkNormWindowAnalyticFeed
    fields
    criterion
    (Norm115.NormWindowClosureCriterion.upperNormWindowClosedInternally
      criterion)
    (Norm115.NormWindowClosureCriterion.upperNormWindowClosedInternallyIsTrue
      criterion)
    (Norm115.NormWindowClosureCriterion.lowerNormWindowClosedInternally
      criterion)
    (Norm115.NormWindowClosureCriterion.lowerNormWindowClosedInternallyIsTrue
      criterion)
    (Norm115.AdmissibleAWindow.windowRecorded
      (Norm115.SuppliedNormWindowFields.admissibleWindow fields))
    (Norm115.AdmissibleAWindow.windowRecordedIsTrue
      (Norm115.SuppliedNormWindowFields.admissibleWindow fields))
    (Norm115.NormWindowClosureCriterion.conditionalCriterionProvedHere
      criterion)
    (Norm115.NormWindowClosureCriterion.conditionalCriterionProvedHereIsTrue
      criterion)
    externalNormWindowClosedHere
    refl
    normAnalyticFeedText
    feed-inhabited
  where
    criterion : Norm115.NormWindowClosureCriterion
    criterion =
      Norm115.normWindowClosureCriterionFromSupplies fields

record QuotientGaugeAnalyticFeed : Setω where
  constructor mkQuotientGaugeAnalyticFeed
  field
    gaugeQuotientInputs :
      Gauge114.GaugeQuotientClosureInputs
    gaugeQuotientCriterion :
      Gauge114.GaugeQuotientClosureCriterion
    localSectionFeedRecorded :
      Bool
    holonomyNaturalityFeedRecorded :
      Bool
    mollifierRenormalizationFeedRecorded :
      Bool
    physicalProjectionFeedRecorded :
      Bool
    orbitInfimumFeedRecorded :
      Bool
    projectionContractionFeedRecorded :
      Bool
    representativeIndependenceFeedRecorded :
      Bool
    quotientGaugeCriterionClosed :
      Bool
    quotientGaugeCriterionClosedIsTrue :
      quotientGaugeCriterionClosed ≡ true
    analyticFeedsDischargedHere :
      Bool
    analyticFeedsDischargedHereIsFalse :
      analyticFeedsDischargedHere ≡ false
    statement :
      String
    status :
      ReducerStatus

quotientGaugeAnalyticFeedFromInputs :
  Gauge114.GaugeQuotientClosureInputs →
  QuotientGaugeAnalyticFeed
quotientGaugeAnalyticFeedFromInputs inputs =
  mkQuotientGaugeAnalyticFeed
    inputs
    criterion
    true
    true
    true
    true
    true
    true
    true
    (Gauge114.GaugeQuotientClosureCriterion.quotientDescentGaugeCovarianceClosureSatisfied
      criterion)
    refl
    (Gauge114.GaugeQuotientClosureCriterion.analyticInputsDischarged
      criterion)
    (Gauge114.GaugeQuotientClosureCriterion.analyticInputsDischargedIsFalse
      criterion)
    quotientGaugeAnalyticFeedText
    feed-inhabited
  where
    criterion : Gauge114.GaugeQuotientClosureCriterion
    criterion =
      Gauge114.closureCriterionFromInputs inputs

record PackageConstantCompatibility : Setω where
  constructor mkPackageConstantCompatibility
  field
    uniformConstants :
      Uniform114.ConsumedSprint113Constants
    normPackageUse :
      Norm115.PackageConstantUse
    uniformPackageConstant :
      Nat
    normPackageConstant :
      Nat
    reducerPackageConstant :
      Nat
    uniformPackageConstantIs645120 :
      uniformPackageConstant ≡ 645120
    normPackageConstantIs645120 :
      normPackageConstant ≡ 645120
    reducerPackageConstantIs645120 :
      reducerPackageConstant ≡ 645120
    uniformConstantAgrees :
      uniformPackageConstant ≡
        Uniform114.ConsumedSprint113Constants.packageConstant uniformConstants
    normConstantAgrees :
      normPackageConstant ≡
        Norm115.PackageConstantUse.packageConstant normPackageUse
    reducerConstantAgreesWithNorm :
      reducerPackageConstant ≡ normPackageConstant
    productIdentity :
      16 * 32 * 12 * 15 * 7 ≡ reducerPackageConstant
    statement :
      String
    status :
      ReducerStatus

canonicalPackageConstantCompatibility :
  PackageConstantCompatibility
canonicalPackageConstantCompatibility =
  mkPackageConstantCompatibility
    Uniform114.canonicalConsumedSprint113Constants
    Norm115.canonicalPackageConstantUse
    645120
    645120
    645120
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    packageConstantCompatibilityText
    constant-compatible

record ReducerInputs : Setω where
  constructor mkReducerInputs
  field
    sprint115Receipt :
      Norm115.YMSprint115NormWindowClosureCriterionReceipt
    normWindowFeed :
      NormWindowAnalyticFeed
    quotientGaugeFeed :
      QuotientGaugeAnalyticFeed
    packageCompatibility :
      PackageConstantCompatibility

record ReducerClosure : Setω where
  constructor mkReducerClosure
  field
    inputs :
      ReducerInputs
    closedCriterion :
      Norm115.NormWindowClosureCriterion
    packageConstant :
      Nat
    packageConstantIs645120 :
      packageConstant ≡ 645120
    normCriterionClosed :
      Bool
    normCriterionClosedIsTrue :
      normCriterionClosed ≡ true
    upperNormWindowClosedInternally :
      Bool
    upperNormWindowClosedInternallyIsTrue :
      upperNormWindowClosedInternally ≡ true
    lowerNormWindowClosedInternally :
      Bool
    lowerNormWindowClosedInternallyIsTrue :
      lowerNormWindowClosedInternally ≡ true
    quotientGaugeCriterionClosed :
      Bool
    quotientGaugeCriterionClosedIsTrue :
      quotientGaugeCriterionClosed ≡ true
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    externalAnalyticClosurePromoted :
      Bool
    externalAnalyticClosurePromotedIsFalse :
      externalAnalyticClosurePromoted ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    conclusion :
      String
    blockedBoundary :
      String
    status :
      ReducerStatus

reducerClosureFromInputs :
  ReducerInputs →
  ReducerClosure
reducerClosureFromInputs inputs =
  mkReducerClosure
    inputs
    criterion
    (PackageConstantCompatibility.reducerPackageConstant compatibility)
    (PackageConstantCompatibility.reducerPackageConstantIs645120
      compatibility)
    normCriterionClosedHere
    refl
    (Norm115.NormWindowClosureCriterion.upperNormWindowClosedInternally
      criterion)
    (Norm115.NormWindowClosureCriterion.upperNormWindowClosedInternallyIsTrue
      criterion)
    (Norm115.NormWindowClosureCriterion.lowerNormWindowClosedInternally
      criterion)
    (Norm115.NormWindowClosureCriterion.lowerNormWindowClosedInternallyIsTrue
      criterion)
    (QuotientGaugeAnalyticFeed.quotientGaugeCriterionClosed gaugeFeed)
    (QuotientGaugeAnalyticFeed.quotientGaugeCriterionClosedIsTrue gaugeFeed)
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    externalAnalyticClosurePromotedHere
    refl
    clayYangMillsPromoted
    refl
    reducerStatementText
    blockedAnalyticClosureText
    conditionally-closed
  where
    normFeed : NormWindowAnalyticFeed
    normFeed =
      ReducerInputs.normWindowFeed inputs

    gaugeFeed : QuotientGaugeAnalyticFeed
    gaugeFeed =
      ReducerInputs.quotientGaugeFeed inputs

    compatibility : PackageConstantCompatibility
    compatibility =
      ReducerInputs.packageCompatibility inputs

    criterion : Norm115.NormWindowClosureCriterion
    criterion =
      NormWindowAnalyticFeed.sprint115Criterion normFeed

record BlockedAnalyticClosureBoundary : Set where
  constructor mkBlockedAnalyticClosureBoundary
  field
    localJacobianClosedHere :
      Bool
    localJacobianClosedHereIsFalse :
      localJacobianClosedHere ≡ false
    quotientNormComparisonClosedHere :
      Bool
    quotientNormComparisonClosedHereIsFalse :
      quotientNormComparisonClosedHere ≡ false
    gaugeCovarianceClosedHere :
      Bool
    gaugeCovarianceClosedHereIsFalse :
      gaugeCovarianceClosedHere ≡ false
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    statement :
      String
    status :
      ReducerStatus

canonicalBlockedAnalyticClosureBoundary :
  BlockedAnalyticClosureBoundary
canonicalBlockedAnalyticClosureBoundary =
  mkBlockedAnalyticClosureBoundary
    Local113.localJacobianEstimateProvedHere
    refl
    Quot113.quotientNormComparisonEstimateClosedHere
    refl
    Gauge113.gaugeCovarianceEstimateClosedHere
    refl
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    clayYangMillsPromoted
    refl
    blockedAnalyticClosureText
    blocked-false

record ReducerTheoremBoundary : Set where
  constructor mkReducerTheoremBoundary
  field
    normCriterionClosed :
      Bool
    normCriterionClosedIsTrue :
      normCriterionClosed ≡ true
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    terminalClayClaimPromotedFlag :
      Bool
    terminalClayClaimPromotedFlagIsFalse :
      terminalClayClaimPromotedFlag ≡ false
    clayYangMillsPromotedFlag :
      Bool
    clayYangMillsPromotedFlagIsFalse :
      clayYangMillsPromotedFlag ≡ false
    theoremBoundaryText :
      String

canonicalReducerTheoremBoundary :
  ReducerTheoremBoundary
canonicalReducerTheoremBoundary =
  mkReducerTheoremBoundary
    normCriterionClosedHere
    refl
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    terminalClayClaimPromoted
    refl
    clayYangMillsPromoted
    refl
    blockedAnalyticClosureText

record YMSprint116NormGaugeWindowClosureReducerReceipt : Setω where
  constructor mkYMSprint116NormGaugeWindowClosureReducerReceipt
  field
    sprint :
      Nat
    sourcePath :
      String
    reducerInputs :
      ReducerInputs
    reducerClosure :
      ReducerClosure
    blockedAnalyticClosureBoundary :
      BlockedAnalyticClosureBoundary
    theoremBoundary :
      ReducerTheoremBoundary
    lanes :
      List ReducerLane
    sourcePaths :
      List String
    evidenceLedger :
      List String
    recorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint116NormGaugeWindowClosureReducerReceipt public

canonicalNormWindowAnalyticFeed :
  NormWindowAnalyticFeed
canonicalNormWindowAnalyticFeed =
  normWindowAnalyticFeedFromSupplies
    Norm115.canonicalSuppliedNormWindowFields

canonicalQuotientGaugeAnalyticFeed :
  QuotientGaugeAnalyticFeed
canonicalQuotientGaugeAnalyticFeed =
  quotientGaugeAnalyticFeedFromInputs
    Gauge114.canonicalGaugeQuotientClosureInputs

canonicalReducerInputs :
  ReducerInputs
canonicalReducerInputs =
  mkReducerInputs
    Norm115.canonicalReceipt
    canonicalNormWindowAnalyticFeed
    canonicalQuotientGaugeAnalyticFeed
    canonicalPackageConstantCompatibility

canonicalReducerClosure :
  ReducerClosure
canonicalReducerClosure =
  reducerClosureFromInputs canonicalReducerInputs

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  reducerStatementText
  ∷ normAnalyticFeedText
  ∷ Norm115.normWindowCriterionStatementText
  ∷ quotientGaugeAnalyticFeedText
  ∷ Gauge114.criterionStatementText
  ∷ packageConstantCompatibilityText
  ∷ Uniform114.constantAssemblyText
  ∷ Local113.combinedConstantText
  ∷ blockedAnalyticClosureText
  ∷ Norm115.nonPromotionBoundaryText
  ∷ []

canonicalYMSprint116NormGaugeWindowClosureReducerReceipt :
  YMSprint116NormGaugeWindowClosureReducerReceipt
canonicalYMSprint116NormGaugeWindowClosureReducerReceipt =
  mkYMSprint116NormGaugeWindowClosureReducerReceipt
    sprintNumber
    modulePath
    canonicalReducerInputs
    canonicalReducerClosure
    canonicalBlockedAnalyticClosureBoundary
    canonicalReducerTheoremBoundary
    canonicalReducerLanes
    (sprint115SourcePath
     ∷ uniform114SourcePath
     ∷ gauge114SourcePath
     ∷ local113SourcePath
     ∷ quotient113SourcePath
     ∷ gauge113SourcePath
     ∷ modulePath
     ∷ [])
    canonicalEvidenceLedger
    normGaugeWindowReducerRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint116NormGaugeWindowClosureReducerReceipt
canonicalReceipt =
  canonicalYMSprint116NormGaugeWindowClosureReducerReceipt

canonicalNormCriterionClosedHere :
  ReducerClosure.normCriterionClosed
    (reducerClosure canonicalReceipt) ≡ true
canonicalNormCriterionClosedHere =
  refl

canonicalExternalNormWindowClosedHereIsFalse :
  ReducerClosure.externalNormWindowClosed
    (reducerClosure canonicalReceipt) ≡ false
canonicalExternalNormWindowClosedHereIsFalse =
  refl

canonicalUnconditionalNormWindowTheoremProvedHereIsFalse :
  ReducerClosure.unconditionalNormWindowTheoremProved
    (reducerClosure canonicalReceipt) ≡ false
canonicalUnconditionalNormWindowTheoremProvedHereIsFalse =
  refl

canonicalQuotientGaugeAnalyticFeedsDischargedHereIsFalse :
  ReducerClosure.quotientGaugeAnalyticFeedsDischarged
    (reducerClosure canonicalReceipt) ≡ false
canonicalQuotientGaugeAnalyticFeedsDischargedHereIsFalse =
  refl

canonicalPackageConstantIs645120 :
  ReducerClosure.packageConstant
    (reducerClosure canonicalReceipt) ≡ 645120
canonicalPackageConstantIs645120 =
  refl

canonicalPackageConstantProduct :
  16 * 32 * 12 * 15 * 7 ≡
  ReducerClosure.packageConstant (reducerClosure canonicalReceipt)
canonicalPackageConstantProduct =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalTerminalClayClaimPromotedIsFalse :
  ReducerTheoremBoundary.terminalClayClaimPromotedFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalTerminalClayClaimPromotedIsFalse =
  refl

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
