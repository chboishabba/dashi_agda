module DASHI.Physics.Closure.YMSprint115NormWindowClosureCriterion where

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

------------------------------------------------------------------------
-- Sprint115 norm-window closure criterion.
--
-- This module advances the Sprint114 uniform constant assembly into a
-- conditional norm-window closure criterion.  It packages the upper and
-- lower norm estimate supplies, quotient/gauge feeds, the concrete
-- C_package=645120 ledger, and an admissible a-window.  The builder closes
-- only the internal criterion from those supplied fields.  External
-- analytic estimate theorems remain explicit open flags.

sprintNumber : Nat
sprintNumber = 115

modulePath : String
modulePath =
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

normWindowClosureCriterionRecorded : Bool
normWindowClosureCriterionRecorded = true

conditionalNormWindowCriterionProvedHere : Bool
conditionalNormWindowCriterionProvedHere = true

unconditionalNormWindowTheoremProvedHere : Bool
unconditionalNormWindowTheoremProvedHere = false

externalAnalyticEstimatesClosedHere : Bool
externalAnalyticEstimatesClosedHere = false

quotientGaugeAnalyticFeedsDischargedHere : Bool
quotientGaugeAnalyticFeedsDischargedHere = false

terminalClayClaimPromoted : Bool
terminalClayClaimPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

normWindowCriterionStatementText : String
normWindowCriterionStatementText =
  "Sprint115 criterion: supplied upper and lower norm estimates, the Sprint114 quotient/gauge closure feeds, and the admissible a-window imply the internal norm-window closure criterion with package constant 645120."

upperNormSupplyText : String
upperNormSupplyText =
  "Upper norm estimate supply: local Jacobian control, chart density control, finite overlap summation, derivative-loss absorption, quotient comparison, and Sprint112 upper-reduction compatibility are treated as supplied fields."

lowerNormSupplyText : String
lowerNormSupplyText =
  "Lower norm estimate supply: the same Sprint113 constant ledger and supplied analytic fields feed the Sprint112 lower-reduction side of the uniform norm comparison."

quotientGaugeFeedText : String
quotientGaugeFeedText =
  "Quotient/gauge feed: Sprint114 gauge-quotient closure inputs are consumed as supplied local-section, holonomy-naturality, covariance, projection-compatibility, orbit-infimum, contraction, and representative-independence records."

admissibleWindowText : String
admissibleWindowText =
  "Admissible a-window: 0 < a <= a0 on the Sprint112/Sprint113 physical quotient comparison surface, using the same local charts, common carrier, and quotient representatives recorded upstream."

externalAnalyticBlockerText : String
externalAnalyticBlockerText =
  "External analytic estimates remain open: Sprint115 does not prove the local Jacobian, density, overlap, derivative-loss, quotient comparison, gauge covariance, quotient descent, projection contraction, or representative-independence estimates."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint115 records only a conditional norm-window closure criterion; it proves no unconditional norm-window theorem, no weak compactness theorem, no spectral gap, no mass gap, and no Clay Yang-Mills promotion."

data NormWindowLane : Set where
  imported-sprint114-uniform-lane :
    NormWindowLane
  imported-sprint114-gauge-lane :
    NormWindowLane
  upper-norm-estimate-supply-lane :
    NormWindowLane
  lower-norm-estimate-supply-lane :
    NormWindowLane
  quotient-gauge-feed-lane :
    NormWindowLane
  package-constant-lane :
    NormWindowLane
  admissible-window-lane :
    NormWindowLane
  conditional-criterion-lane :
    NormWindowLane
  external-blocker-lane :
    NormWindowLane
  receipt-lane :
    NormWindowLane

data NormWindowStatus : Set where
  imported-sprint114-uniform :
    NormWindowStatus
  imported-sprint114-gauge :
    NormWindowStatus
  supply-recorded :
    NormWindowStatus
  feed-recorded :
    NormWindowStatus
  package-constant-recorded :
    NormWindowStatus
  admissible-window-recorded :
    NormWindowStatus
  conditional-criterion-recorded :
    NormWindowStatus
  external-estimate-open :
    NormWindowStatus
  fail-closed-nonpromotion :
    NormWindowStatus

canonicalNormWindowLanes : List NormWindowLane
canonicalNormWindowLanes =
  imported-sprint114-uniform-lane
  ∷ imported-sprint114-gauge-lane
  ∷ upper-norm-estimate-supply-lane
  ∷ lower-norm-estimate-supply-lane
  ∷ quotient-gauge-feed-lane
  ∷ package-constant-lane
  ∷ admissible-window-lane
  ∷ conditional-criterion-lane
  ∷ external-blocker-lane
  ∷ receipt-lane
  ∷ []

record ImportedSprint114Surface : Setω where
  constructor mkImportedSprint114Surface
  field
    uniformConstantAssemblyReceipt :
      Uniform114.YMSprint114UniformNormConstantAssemblyReceipt
    gaugeQuotientClosureReceipt :
      Gauge114.YMSprint114GaugeQuotientClosureCriterionReceipt
    uniformAssemblyRecorded :
      Bool
    gaugeClosureRecorded :
      Bool
    packageConstant :
      Nat
    packageConstantIs645120 :
      packageConstant ≡ 645120
    uniformCriterionStillExternal :
      Bool
    uniformCriterionStillExternalIsFalse :
      Uniform114.AssemblyTheoremBoundary.uniformUpperLowerCriterionClosedHereFlag
        (Uniform114.theoremBoundary uniformConstantAssemblyReceipt) ≡ false
    gaugeAnalyticInputsStillExternal :
      Bool
    gaugeAnalyticInputsStillExternalIsFalse :
      Gauge114.GaugeQuotientClosureCriterion.analyticInputsDischarged
        (Gauge114.YMSprint114GaugeQuotientClosureCriterionReceipt.criterion
          gaugeQuotientClosureReceipt)
      ≡ false
    uniform114ClayPromotedFalse :
      Uniform114.clayYangMillsPromotedHere uniformConstantAssemblyReceipt
      ≡ false
    gauge114ClayPromotedFalse :
      Gauge114.YMSprint114GaugeQuotientClosureCriterionReceipt.clayYangMillsPromotedReceipt
        gaugeQuotientClosureReceipt
      ≡ false

record UpperNormEstimateSupply : Set where
  constructor mkUpperNormEstimateSupply
  field
    localJacobianSupplied :
      Bool
    localJacobianSuppliedIsTrue :
      localJacobianSupplied ≡ true
    chartDensitySupplied :
      Bool
    chartDensitySuppliedIsTrue :
      chartDensitySupplied ≡ true
    finiteOverlapSupplied :
      Bool
    finiteOverlapSuppliedIsTrue :
      finiteOverlapSupplied ≡ true
    derivativeLossSupplied :
      Bool
    derivativeLossSuppliedIsTrue :
      derivativeLossSupplied ≡ true
    quotientComparisonSupplied :
      Bool
    quotientComparisonSuppliedIsTrue :
      quotientComparisonSupplied ≡ true
    sprint112UpperReductionCompatible :
      Bool
    sprint112UpperReductionCompatibleIsTrue :
      sprint112UpperReductionCompatible ≡ true
    statement :
      String

record LowerNormEstimateSupply : Set where
  constructor mkLowerNormEstimateSupply
  field
    localJacobianSupplied :
      Bool
    localJacobianSuppliedIsTrue :
      localJacobianSupplied ≡ true
    chartDensitySupplied :
      Bool
    chartDensitySuppliedIsTrue :
      chartDensitySupplied ≡ true
    finiteOverlapSupplied :
      Bool
    finiteOverlapSuppliedIsTrue :
      finiteOverlapSupplied ≡ true
    derivativeLossSupplied :
      Bool
    derivativeLossSuppliedIsTrue :
      derivativeLossSupplied ≡ true
    quotientComparisonSupplied :
      Bool
    quotientComparisonSuppliedIsTrue :
      quotientComparisonSupplied ≡ true
    sprint112LowerReductionCompatible :
      Bool
    sprint112LowerReductionCompatibleIsTrue :
      sprint112LowerReductionCompatible ≡ true
    statement :
      String

record QuotientGaugeFeedPackage : Setω where
  constructor mkQuotientGaugeFeedPackage
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
    quotientGaugeCriterionSatisfied :
      Bool
    quotientGaugeCriterionSatisfiedIsTrue :
      quotientGaugeCriterionSatisfied ≡ true
    externalAnalyticInputsDischarged :
      Bool
    externalAnalyticInputsDischargedIsFalse :
      externalAnalyticInputsDischarged ≡ false
    statement :
      String

record PackageConstantUse : Set where
  constructor mkPackageConstantUse
  field
    constants :
      Uniform114.ConsumedSprint113Constants
    packageConstant :
      Nat
    packageConstantIsCanonical :
      packageConstant ≡
        Uniform114.ConsumedSprint113Constants.packageConstant constants
    packageConstantIs645120 :
      packageConstant ≡ 645120
    productIdentity :
      16 * 32 * 12 * 15 * 7 ≡ packageConstant
    usedForUpperEstimate :
      Bool
    usedForUpperEstimateIsTrue :
      usedForUpperEstimate ≡ true
    usedForLowerEstimate :
      Bool
    usedForLowerEstimateIsTrue :
      usedForLowerEstimate ≡ true
    status :
      NormWindowStatus

record AdmissibleAWindow : Set where
  constructor mkAdmissibleAWindow
  field
    windowRecorded :
      Bool
    windowRecordedIsTrue :
      windowRecorded ≡ true
    positiveCutoffRequired :
      Bool
    boundedByA0 :
      Bool
    commonCarrierFixed :
      Bool
    quotientRepresentativesFixed :
      Bool
    localChartsFixed :
      Bool
    compatibleWithSprint113Window :
      Bool
    sprint113WindowText :
      String
    statement :
      String
    status :
      NormWindowStatus

record SuppliedNormWindowFields : Setω where
  constructor mkSuppliedNormWindowFields
  field
    importedSurface :
      ImportedSprint114Surface
    upperSupply :
      UpperNormEstimateSupply
    lowerSupply :
      LowerNormEstimateSupply
    quotientGaugeFeeds :
      QuotientGaugeFeedPackage
    packageUse :
      PackageConstantUse
    admissibleWindow :
      AdmissibleAWindow

suppliedFieldsToSprint114AnalyticFields :
  SuppliedNormWindowFields →
  Uniform114.SuppliedAnalyticEstimateFields
suppliedFieldsToSprint114AnalyticFields fields =
  Uniform114.mkSuppliedAnalyticEstimateFields
    (UpperNormEstimateSupply.localJacobianSupplied upper)
    (UpperNormEstimateSupply.localJacobianSuppliedIsTrue upper)
    (UpperNormEstimateSupply.chartDensitySupplied upper)
    (UpperNormEstimateSupply.chartDensitySuppliedIsTrue upper)
    (UpperNormEstimateSupply.finiteOverlapSupplied upper)
    (UpperNormEstimateSupply.finiteOverlapSuppliedIsTrue upper)
    (UpperNormEstimateSupply.derivativeLossSupplied upper)
    (UpperNormEstimateSupply.derivativeLossSuppliedIsTrue upper)
    (UpperNormEstimateSupply.quotientComparisonSupplied upper)
    (UpperNormEstimateSupply.quotientComparisonSuppliedIsTrue upper)
    (UpperNormEstimateSupply.sprint112UpperReductionCompatible upper)
    (UpperNormEstimateSupply.sprint112UpperReductionCompatibleIsTrue upper)
    (LowerNormEstimateSupply.sprint112LowerReductionCompatible lower)
    (LowerNormEstimateSupply.sprint112LowerReductionCompatibleIsTrue lower)
    (PackageConstantUse.constants package)
  where
    upper : UpperNormEstimateSupply
    upper =
      SuppliedNormWindowFields.upperSupply fields

    lower : LowerNormEstimateSupply
    lower =
      SuppliedNormWindowFields.lowerSupply fields

    package : PackageConstantUse
    package =
      SuppliedNormWindowFields.packageUse fields

record NormWindowClosureCriterion : Setω where
  constructor mkNormWindowClosureCriterion
  field
    suppliedFields :
      SuppliedNormWindowFields
    sprint114AnalyticFields :
      Uniform114.SuppliedAnalyticEstimateFields
    uniformUpperLowerCriterion :
      Uniform114.UniformUpperLowerNormCriterion
    gaugeQuotientCriterion :
      Gauge114.GaugeQuotientClosureCriterion
    admissibleWindow :
      AdmissibleAWindow
    packageConstant :
      Nat
    packageConstantIs645120 :
      packageConstant ≡ 645120
    upperNormWindowClosedInternally :
      Bool
    upperNormWindowClosedInternallyIsTrue :
      upperNormWindowClosedInternally ≡ true
    lowerNormWindowClosedInternally :
      Bool
    lowerNormWindowClosedInternallyIsTrue :
      lowerNormWindowClosedInternally ≡ true
    quotientGaugeFeedsUsed :
      Bool
    quotientGaugeFeedsUsedIsTrue :
      quotientGaugeFeedsUsed ≡ true
    admissibleWindowUsed :
      Bool
    admissibleWindowUsedIsTrue :
      admissibleWindowUsed ≡ true
    conditionalCriterionProvedHere :
      Bool
    conditionalCriterionProvedHereIsTrue :
      conditionalCriterionProvedHere ≡ true
    unconditionalNormWindowTheorem :
      Bool
    unconditionalNormWindowTheoremIsFalse :
      unconditionalNormWindowTheorem ≡ false
    externalAnalyticEstimatesClosed :
      Bool
    externalAnalyticEstimatesClosedIsFalse :
      externalAnalyticEstimatesClosed ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    conclusion :
      String
    status :
      NormWindowStatus

normWindowClosureCriterionFromSupplies :
  SuppliedNormWindowFields →
  NormWindowClosureCriterion
normWindowClosureCriterionFromSupplies fields =
  mkNormWindowClosureCriterion
    fields
    analyticFields
    (Uniform114.suppliedFieldsToUniformUpperLowerNormCriterion analyticFields)
    (QuotientGaugeFeedPackage.gaugeQuotientCriterion quotientGauge)
    (SuppliedNormWindowFields.admissibleWindow fields)
    (PackageConstantUse.packageConstant package)
    (PackageConstantUse.packageConstantIs645120 package)
    true
    refl
    true
    refl
    (QuotientGaugeFeedPackage.quotientGaugeCriterionSatisfied quotientGauge)
    (QuotientGaugeFeedPackage.quotientGaugeCriterionSatisfiedIsTrue
      quotientGauge)
    (AdmissibleAWindow.windowRecorded
      (SuppliedNormWindowFields.admissibleWindow fields))
    (AdmissibleAWindow.windowRecordedIsTrue
      (SuppliedNormWindowFields.admissibleWindow fields))
    conditionalNormWindowCriterionProvedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    externalAnalyticEstimatesClosedHere
    refl
    clayYangMillsPromoted
    refl
    normWindowCriterionStatementText
    conditional-criterion-recorded
  where
    analyticFields : Uniform114.SuppliedAnalyticEstimateFields
    analyticFields =
      suppliedFieldsToSprint114AnalyticFields fields

    quotientGauge : QuotientGaugeFeedPackage
    quotientGauge =
      SuppliedNormWindowFields.quotientGaugeFeeds fields

    package : PackageConstantUse
    package =
      SuppliedNormWindowFields.packageUse fields

record ExternalAnalyticEstimateFlags : Set where
  constructor mkExternalAnalyticEstimateFlags
  field
    localJacobianClosedHere :
      Bool
    localJacobianClosedHereIsFalse :
      localJacobianClosedHere ≡ false
    chartDensityClosedHere :
      Bool
    chartDensityClosedHereIsFalse :
      chartDensityClosedHere ≡ false
    finiteOverlapClosedHere :
      Bool
    finiteOverlapClosedHereIsFalse :
      finiteOverlapClosedHere ≡ false
    derivativeLossClosedHere :
      Bool
    derivativeLossClosedHereIsFalse :
      derivativeLossClosedHere ≡ false
    quotientNormComparisonClosedHere :
      Bool
    quotientNormComparisonClosedHereIsFalse :
      quotientNormComparisonClosedHere ≡ false
    gaugeCovarianceClosedHere :
      Bool
    gaugeCovarianceClosedHereIsFalse :
      gaugeCovarianceClosedHere ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    unconditionalNormWindowTheorem :
      Bool
    unconditionalNormWindowTheoremIsFalse :
      unconditionalNormWindowTheorem ≡ false
    statement :
      String
    status :
      NormWindowStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    conditionalCriterionProved :
      Bool
    conditionalCriterionProvedIsTrue :
      conditionalCriterionProved ≡ true
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    externalAnalyticEstimatesClosed :
      Bool
    externalAnalyticEstimatesClosedIsFalse :
      externalAnalyticEstimatesClosed ≡ false
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

record YMSprint115NormWindowClosureCriterionReceipt : Setω where
  constructor mkYMSprint115NormWindowClosureCriterionReceipt
  field
    sprint :
      Nat
    sourcePath :
      String
    importedSurface :
      ImportedSprint114Surface
    suppliedFields :
      SuppliedNormWindowFields
    criterion :
      NormWindowClosureCriterion
    externalAnalyticFlags :
      ExternalAnalyticEstimateFlags
    theoremBoundary :
      TheoremBoundary
    lanes :
      List NormWindowLane
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

open YMSprint115NormWindowClosureCriterionReceipt public

canonicalImportedSprint114Surface : ImportedSprint114Surface
canonicalImportedSprint114Surface =
  mkImportedSprint114Surface
    Uniform114.canonicalReceipt
    Gauge114.canonicalReceipt
    Uniform114.uniformNormConstantAssemblyRecorded
    Gauge114.gaugeQuotientClosureCriterionRecorded
    Uniform114.canonicalReceiptPackageConstant
    Uniform114.canonicalReceiptPackageConstantIs645120
    (Uniform114.AssemblyTheoremBoundary.uniformUpperLowerCriterionClosedHereFlag
      (Uniform114.theoremBoundary Uniform114.canonicalReceipt))
    refl
    (Gauge114.GaugeQuotientClosureCriterion.analyticInputsDischarged
      (Gauge114.YMSprint114GaugeQuotientClosureCriterionReceipt.criterion
        Gauge114.canonicalReceipt))
    refl
    Uniform114.canonicalReceiptClayYangMillsPromotedIsFalse
    Gauge114.canonicalClayYangMillsPromotedIsFalse

canonicalUpperNormEstimateSupply : UpperNormEstimateSupply
canonicalUpperNormEstimateSupply =
  mkUpperNormEstimateSupply
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    upperNormSupplyText

canonicalLowerNormEstimateSupply : LowerNormEstimateSupply
canonicalLowerNormEstimateSupply =
  mkLowerNormEstimateSupply
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    lowerNormSupplyText

canonicalQuotientGaugeFeedPackage : QuotientGaugeFeedPackage
canonicalQuotientGaugeFeedPackage =
  mkQuotientGaugeFeedPackage
    Gauge114.canonicalGaugeQuotientClosureInputs
    Gauge114.canonicalGaugeQuotientClosureCriterion
    true
    true
    true
    true
    true
    true
    true
    (Gauge114.GaugeQuotientClosureCriterion.quotientDescentGaugeCovarianceClosureSatisfied
      Gauge114.canonicalGaugeQuotientClosureCriterion)
    refl
    (Gauge114.GaugeQuotientClosureCriterion.analyticInputsDischarged
      Gauge114.canonicalGaugeQuotientClosureCriterion)
    refl
    quotientGaugeFeedText

canonicalPackageConstantUse : PackageConstantUse
canonicalPackageConstantUse =
  mkPackageConstantUse
    Uniform114.canonicalConsumedSprint113Constants
    645120
    refl
    refl
    refl
    true
    refl
    true
    refl
    package-constant-recorded

canonicalAdmissibleAWindow : AdmissibleAWindow
canonicalAdmissibleAWindow =
  mkAdmissibleAWindow
    true
    refl
    true
    true
    true
    true
    true
    true
    Local113.admissibleWindowText
    admissibleWindowText
    admissible-window-recorded

canonicalSuppliedNormWindowFields : SuppliedNormWindowFields
canonicalSuppliedNormWindowFields =
  mkSuppliedNormWindowFields
    canonicalImportedSprint114Surface
    canonicalUpperNormEstimateSupply
    canonicalLowerNormEstimateSupply
    canonicalQuotientGaugeFeedPackage
    canonicalPackageConstantUse
    canonicalAdmissibleAWindow

canonicalNormWindowClosureCriterion :
  NormWindowClosureCriterion
canonicalNormWindowClosureCriterion =
  normWindowClosureCriterionFromSupplies canonicalSuppliedNormWindowFields

canonicalExternalAnalyticEstimateFlags :
  ExternalAnalyticEstimateFlags
canonicalExternalAnalyticEstimateFlags =
  mkExternalAnalyticEstimateFlags
    Local113.localJacobianEstimateProvedHere
    refl
    Local113.chartVolumeDensityTheoremProvedHere
    refl
    Local113.finiteOverlapSummationTheoremProvedHere
    refl
    Local113.derivativeLossAbsorptionProvedHere
    refl
    Quot113.quotientNormComparisonEstimateClosedHere
    refl
    Gauge113.gaugeCovarianceEstimateClosedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    externalAnalyticBlockerText
    external-estimate-open

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    conditionalNormWindowCriterionProvedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    externalAnalyticEstimatesClosedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    terminalClayClaimPromoted
    refl
    clayYangMillsPromoted
    refl
    nonPromotionBoundaryText

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  normWindowCriterionStatementText
  ∷ upperNormSupplyText
  ∷ lowerNormSupplyText
  ∷ Uniform114.constantAssemblyText
  ∷ Uniform114.criterionImplicationText
  ∷ quotientGaugeFeedText
  ∷ Gauge114.criterionStatementText
  ∷ admissibleWindowText
  ∷ Local113.admissibleWindowText
  ∷ externalAnalyticBlockerText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint115NormWindowClosureCriterionReceipt :
  YMSprint115NormWindowClosureCriterionReceipt
canonicalYMSprint115NormWindowClosureCriterionReceipt =
  mkYMSprint115NormWindowClosureCriterionReceipt
    sprintNumber
    modulePath
    canonicalImportedSprint114Surface
    canonicalSuppliedNormWindowFields
    canonicalNormWindowClosureCriterion
    canonicalExternalAnalyticEstimateFlags
    canonicalTheoremBoundary
    canonicalNormWindowLanes
    (uniform114SourcePath
     ∷ gauge114SourcePath
     ∷ local113SourcePath
     ∷ quotient113SourcePath
     ∷ gauge113SourcePath
     ∷ modulePath
     ∷ [])
    canonicalEvidenceLedger
    normWindowClosureCriterionRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint115NormWindowClosureCriterionReceipt
canonicalReceipt =
  canonicalYMSprint115NormWindowClosureCriterionReceipt

canonicalCriterionConditionalProvedHere :
  NormWindowClosureCriterion.conditionalCriterionProvedHere
    (criterion canonicalReceipt) ≡ true
canonicalCriterionConditionalProvedHere =
  refl

canonicalCriterionUpperClosedInternally :
  NormWindowClosureCriterion.upperNormWindowClosedInternally
    (criterion canonicalReceipt) ≡ true
canonicalCriterionUpperClosedInternally =
  refl

canonicalCriterionLowerClosedInternally :
  NormWindowClosureCriterion.lowerNormWindowClosedInternally
    (criterion canonicalReceipt) ≡ true
canonicalCriterionLowerClosedInternally =
  refl

canonicalCriterionPackageConstant : Nat
canonicalCriterionPackageConstant =
  NormWindowClosureCriterion.packageConstant (criterion canonicalReceipt)

canonicalCriterionPackageConstantIs645120 :
  canonicalCriterionPackageConstant ≡ 645120
canonicalCriterionPackageConstantIs645120 =
  refl

canonicalCriterionConstantProduct :
  16 * 32 * 12 * 15 * 7 ≡ canonicalCriterionPackageConstant
canonicalCriterionConstantProduct =
  refl

canonicalUnconditionalNormWindowTheoremIsFalse :
  NormWindowClosureCriterion.unconditionalNormWindowTheorem
    (criterion canonicalReceipt) ≡ false
canonicalUnconditionalNormWindowTheoremIsFalse =
  refl

canonicalExternalAnalyticEstimatesClosedIsFalse :
  NormWindowClosureCriterion.externalAnalyticEstimatesClosed
    (criterion canonicalReceipt) ≡ false
canonicalExternalAnalyticEstimatesClosedIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalTerminalClayClaimPromotedIsFalse :
  TheoremBoundary.terminalClayClaimPromotedFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalTerminalClayClaimPromotedIsFalse =
  refl

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
