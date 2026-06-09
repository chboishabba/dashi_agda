module DASHI.Physics.Closure.YMSprint113LocalJacobianPartitionEstimate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction
  as Uniform112
import DASHI.Physics.Closure.YMSprint112RenormalizedInterpolationMapCandidate
  as Interp112
import DASHI.Physics.Closure.YMSprint112ContinuumSamplingProjectionMapCandidate
  as Sampling112
import DASHI.Physics.Closure.YMSprint111FiniteContinuumEmbeddingProjectionMaps
  as Maps111

------------------------------------------------------------------------
-- Sprint113 local Jacobian plus partition/multiplicity estimate package.
--
-- This file records the concrete local-estimate bookkeeping that Sprint112
-- asked for: local chart Jacobian comparison, chart-volume/density comparison,
-- finite-overlap summation, partition multiplicity, derivative-loss accounting,
-- map-candidate provenance, and exact blockers.  It is an inhabited evidence
-- package only.  It does not prove a DASHI-native analytic estimate theorem,
-- uniform norm equivalence, weak-compactness feed, mass gap, or Clay promotion.

localJacobianPartitionPackageRecorded : Bool
localJacobianPartitionPackageRecorded = true

localJacobianLedgerRecorded : Bool
localJacobianLedgerRecorded = true

chartVolumeDensityComparisonRecorded : Bool
chartVolumeDensityComparisonRecorded = true

finiteOverlapSummationRecorded : Bool
finiteOverlapSummationRecorded = true

derivativeLossAccountingRecorded : Bool
derivativeLossAccountingRecorded = true

mapCandidateProvenanceRecorded : Bool
mapCandidateProvenanceRecorded = true

localJacobianEstimateProvedHere : Bool
localJacobianEstimateProvedHere = false

partitionMultiplicityEstimateProvedHere : Bool
partitionMultiplicityEstimateProvedHere = false

finiteOverlapSummationTheoremProvedHere : Bool
finiteOverlapSummationTheoremProvedHere = false

chartVolumeDensityTheoremProvedHere : Bool
chartVolumeDensityTheoremProvedHere = false

derivativeLossAbsorptionProvedHere : Bool
derivativeLossAbsorptionProvedHere = false

uniformNormBoundClosedHere : Bool
uniformNormBoundClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprintNumber : Nat
sprintNumber = 113

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint113LocalJacobianPartitionEstimate.agda"

uniform112SourcePath : String
uniform112SourcePath =
  "DASHI/Physics/Closure/YMSprint112UniformNormBoundReduction.agda"

interp112SourcePath : String
interp112SourcePath =
  "DASHI/Physics/Closure/YMSprint112RenormalizedInterpolationMapCandidate.agda"

sampling112SourcePath : String
sampling112SourcePath =
  "DASHI/Physics/Closure/YMSprint112ContinuumSamplingProjectionMapCandidate.agda"

maps111SourcePath : String
maps111SourcePath =
  "DASHI/Physics/Closure/YMSprint111FiniteContinuumEmbeddingProjectionMaps.agda"

admissibleWindowText : String
admissibleWindowText =
  "Sprint113 works over the Sprint112 admissible a-window 0 < a <= a0 and keeps the same finite physical quotient, continuum H_phys carrier, E_a interpolation candidate, and P_a sampling/projection candidate."

localJacobianEstimateText : String
localJacobianEstimateText =
  "Local Jacobian estimate package: on each admissible chart cell Q_i(a), compare the renormalized interpolation/sampling Jacobian J_i(a) with the continuum H_phys density using a recorded constant C_J=16, chart volume constant C_V=8, and density constant C_rho=4."

finiteOverlapSummationText : String
finiteOverlapSummationText =
  "Finite-overlap summation package: the partition chi_i has overlap multiplicity M=12, so a local nonnegative ledger term bounded by B_i contributes at most M times the global chart sum before derivative losses and quotient comparison are applied."

chartVolumeDensityComparisonText : String
chartVolumeDensityComparisonText =
  "Chart-volume/density comparison package: every chart cell uses volume normalization V_i(a) and density rho_i(a) with ledger comparison V_i(a) * rho_i(a) <= C_Vrho * referenceCellMass_i(a), where C_Vrho=32 is recorded as the finite local comparison constant."

derivativeLossAccountingText : String
derivativeLossAccountingText =
  "Derivative-loss accounting package: partition derivatives up to order k=2 are charged to L_1=3 and L_2=5, with total recorded derivative-loss constant L_total=15 before quotient norm comparison."

combinedConstantText : String
combinedConstantText =
  "Combined recorded bookkeeping constant: C_local=16, C_Vrho=32, M=12, L_total=15, C_quot=7, hence the ledger records C_package=645120 as 16*32*12*15*7.  This is a concrete accounting number, not a proved sharp analytic bound."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint113 records local Jacobian and partition/multiplicity estimates as an inhabited package only; it does not close the local analytic estimates, Sprint112 uniform norm bounds, weak compactness, spectral passage, mass gap, or Clay Yang-Mills promotion."

jacobianBlockerText : String
jacobianBlockerText =
  "Exact blocker A: no proof establishes the chartwise Jacobian comparison J_i(a) <= C_J uniformly over all admissible cells, gauge representatives, and a in 0 < a <= a0."

chartVolumeDensityBlockerText : String
chartVolumeDensityBlockerText =
  "Exact blocker B: no proof establishes the chart-volume/density comparison V_i(a) * rho_i(a) <= C_Vrho * referenceCellMass_i(a) under the shared Sprint111/Sprint112 normalization."

finiteOverlapBlockerText : String
finiteOverlapBlockerText =
  "Exact blocker C: no proof establishes that the recorded partition has global multiplicity at most M=12 for every finite-volume exhaustion and all boundary chart refinements."

derivativeLossBlockerText : String
derivativeLossBlockerText =
  "Exact blocker D: no proof absorbs the k<=2 partition derivative losses into the renormalized E_a/P_a local estimate with an a-independent constant."

quotientCompatibilityBlockerText : String
quotientCompatibilityBlockerText =
  "Exact blocker E: no proof shows the local chart estimates descend through finite gauge quotient representatives and continuum physical projection without increasing constants beyond C_quot=7."

uniformReductionBlockerText : String
uniformReductionBlockerText =
  "Exact blocker F: the Sprint112 uniform upper/lower norm reductions remain open because the local Jacobian, partition, chart-volume/density, derivative-loss, and quotient-compatibility theorems are not proved here."

data EstimateLane : Set where
  sprint112-reduction-import :
    EstimateLane
  interpolation-candidate-import :
    EstimateLane
  sampling-candidate-import :
    EstimateLane
  local-jacobian-lane :
    EstimateLane
  chart-volume-density-lane :
    EstimateLane
  finite-overlap-summation-lane :
    EstimateLane
  derivative-loss-lane :
    EstimateLane
  quotient-compatibility-lane :
    EstimateLane
  combined-ledger-lane :
    EstimateLane
  blocker-lane :
    EstimateLane
  receipt-lane :
    EstimateLane

data EstimateStatus : Set where
  imported-sprint112-reduction :
    EstimateStatus
  imported-map-candidate :
    EstimateStatus
  recorded-inhabited :
    EstimateStatus
  concrete-constant-ledger :
    EstimateStatus
  finite-overlap-recorded :
    EstimateStatus
  derivative-loss-recorded :
    EstimateStatus
  exact-blocker-recorded :
    EstimateStatus
  analytic-proof-required :
    EstimateStatus
  fail-closed-nonpromotion :
    EstimateStatus

data EstimateKind : Set where
  local-jacobian-kind :
    EstimateKind
  chart-volume-density-kind :
    EstimateKind
  finite-overlap-kind :
    EstimateKind
  derivative-loss-kind :
    EstimateKind
  quotient-comparison-kind :
    EstimateKind
  combined-package-kind :
    EstimateKind

data BlockerKind : Set where
  jacobian-blocker :
    BlockerKind
  chart-volume-density-blocker :
    BlockerKind
  finite-overlap-blocker :
    BlockerKind
  derivative-loss-blocker :
    BlockerKind
  quotient-compatibility-blocker :
    BlockerKind
  uniform-reduction-blocker :
    BlockerKind
  nonpromotion-blocker :
    BlockerKind

canonicalEstimateLanes : List EstimateLane
canonicalEstimateLanes =
  sprint112-reduction-import
  ∷ interpolation-candidate-import
  ∷ sampling-candidate-import
  ∷ local-jacobian-lane
  ∷ chart-volume-density-lane
  ∷ finite-overlap-summation-lane
  ∷ derivative-loss-lane
  ∷ quotient-compatibility-lane
  ∷ combined-ledger-lane
  ∷ blocker-lane
  ∷ receipt-lane
  ∷ []

record ImportedMapCandidateReceipts : Setω where
  constructor mkImportedMapCandidateReceipts
  field
    uniform112Receipt :
      Uniform112.YMSprint112UniformNormBoundReductionReceipt
    interpolation112Receipt :
      Interp112.YMSprint112RenormalizedInterpolationMapCandidateReceipt
    sampling112Receipt :
      Sampling112.SamplingProjectionCandidateReceipt
    maps111Receipt :
      Maps111.YMSprint111FiniteContinuumEmbeddingProjectionMapsReceipt
    uniform112PromotionFalse :
      Uniform112.clayYangMillsPromotedHere
        Uniform112.canonicalReceipt ≡ false
    interpolation112PromotionFalse :
      Interp112.clayYangMillsPromotedHere
        Interp112.canonicalReceipt ≡ false
    sampling112PromotionFalse :
      Sampling112.clayYangMillsPromotedHere
        Sampling112.canonicalReceipt ≡ false
    maps111PromotionFalse :
      Maps111.clayYangMillsPromoted ≡ false

record ConcreteConstantLedger : Set where
  constructor mkConcreteConstantLedger
  field
    chartJacobianConstant :
      Nat
    chartVolumeConstant :
      Nat
    densityComparisonConstant :
      Nat
    chartVolumeDensityConstant :
      Nat
    overlapMultiplicity :
      Nat
    firstDerivativeLoss :
      Nat
    secondDerivativeLoss :
      Nat
    totalDerivativeLoss :
      Nat
    quotientComparisonConstant :
      Nat
    combinedPackageConstant :
      Nat
    constantsStatement :
      String
    constantsConcrete :
      Bool
    status :
      EstimateStatus

record LocalJacobianLedgerEntry : Set where
  constructor mkLocalJacobianLedgerEntry
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    chartSymbol :
      String
    mapSymbols :
      String
    jacobianSymbol :
      String
    densitySymbol :
      String
    admissibleWindow :
      String
    constantLedger :
      ConcreteConstantLedger
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      EstimateStatus

record ChartVolumeDensityComparison : Set where
  constructor mkChartVolumeDensityComparison
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    chartVolumeSymbol :
      String
    continuumDensitySymbol :
      String
    referenceMassSymbol :
      String
    comparisonConstant :
      Nat
    normalizationSharedWithMaps111 :
      Bool
    normalizationSharedWithSprint112 :
      Bool
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      EstimateStatus

record FiniteOverlapSummation : Set where
  constructor mkFiniteOverlapSummation
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    partitionSymbol :
      String
    localTermSymbol :
      String
    globalSumSymbol :
      String
    multiplicityConstant :
      Nat
    finiteOverlapRecorded :
      Bool
    boundaryRefinementAccounted :
      Bool
    summationFormulaText :
      String
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      EstimateStatus

record DerivativeLossAccount : Set where
  constructor mkDerivativeLossAccount
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    partitionSymbol :
      String
    maxDerivativeOrder :
      Nat
    firstDerivativeLossConstant :
      Nat
    secondDerivativeLossConstant :
      Nat
    totalLossConstant :
      Nat
    chargedAgainstLocalJacobian :
      Bool
    chargedAgainstPartition :
      Bool
    chargedAgainstQuotientComparison :
      Bool
    recordedHere :
      Bool
    absorbedHere :
      Bool
    absorbedHereIsFalse :
      absorbedHere ≡ false
    status :
      EstimateStatus

record QuotientCompatibilityEstimate : Set where
  constructor mkQuotientCompatibilityEstimate
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    finiteQuotientNorm :
      String
    continuumPhysicalNorm :
      String
    quotientConstant :
      Nat
    usesInterpolationCandidate :
      Bool
    usesSamplingCandidate :
      Bool
    usesMaps111Surface :
      Bool
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      EstimateStatus

record CombinedEstimatePackage : Set where
  constructor mkCombinedEstimatePackage
  field
    lane :
      EstimateLane
    kind :
      EstimateKind
    statement :
      String
    localJacobian :
      LocalJacobianLedgerEntry
    chartVolumeDensity :
      ChartVolumeDensityComparison
    finiteOverlapSummation :
      FiniteOverlapSummation
    derivativeLoss :
      DerivativeLossAccount
    quotientCompatibility :
      QuotientCompatibilityEstimate
    combinedConstant :
      Nat
    packageFeedsSprint112Reduction :
      Bool
    packageClosesSprint112ReductionHere :
      Bool
    packageClosesSprint112ReductionHereIsFalse :
      packageClosesSprint112ReductionHere ≡ false
    status :
      EstimateStatus

record BlockerLedgerEntry : Set where
  constructor mkBlockerLedgerEntry
  field
    blocker :
      BlockerKind
    lane :
      EstimateLane
    statement :
      String
    blocksUniformNormClosure :
      Bool
    blocksClayPromotion :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      EstimateStatus

record ExactBlockerLedger : Set where
  constructor mkExactBlockerLedger
  field
    lane :
      EstimateLane
    entries :
      List BlockerLedgerEntry
    jacobianBlocker :
      String
    chartVolumeDensityBlocker :
      String
    finiteOverlapBlocker :
      String
    derivativeLossBlocker :
      String
    quotientCompatibilityBlocker :
      String
    uniformReductionBlocker :
      String
    allBlockersConcrete :
      Bool
    theoremStillOpen :
      Bool
    status :
      EstimateStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    targetStatement :
      String
    nonPromotionStatement :
      String
    localJacobianEstimateProvedHereFlag :
      Bool
    localJacobianEstimateProvedHereFlagIsFalse :
      localJacobianEstimateProvedHereFlag ≡ false
    partitionMultiplicityEstimateProvedHereFlag :
      Bool
    partitionMultiplicityEstimateProvedHereFlagIsFalse :
      partitionMultiplicityEstimateProvedHereFlag ≡ false
    finiteOverlapSummationTheoremProvedHereFlag :
      Bool
    finiteOverlapSummationTheoremProvedHereFlagIsFalse :
      finiteOverlapSummationTheoremProvedHereFlag ≡ false
    chartVolumeDensityTheoremProvedHereFlag :
      Bool
    chartVolumeDensityTheoremProvedHereFlagIsFalse :
      chartVolumeDensityTheoremProvedHereFlag ≡ false
    derivativeLossAbsorptionProvedHereFlag :
      Bool
    derivativeLossAbsorptionProvedHereFlagIsFalse :
      derivativeLossAbsorptionProvedHereFlag ≡ false
    uniformNormBoundClosedHereFlag :
      Bool
    uniformNormBoundClosedHereFlagIsFalse :
      uniformNormBoundClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      EstimateStatus

record YMSprint113LocalJacobianPartitionEstimateReceipt : Setω where
  constructor mkYMSprint113LocalJacobianPartitionEstimateReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedReceipts :
      ImportedMapCandidateReceipts
    constants :
      ConcreteConstantLedger
    localJacobian :
      LocalJacobianLedgerEntry
    chartVolumeDensity :
      ChartVolumeDensityComparison
    finiteOverlap :
      FiniteOverlapSummation
    derivativeLoss :
      DerivativeLossAccount
    quotientCompatibility :
      QuotientCompatibilityEstimate
    combinedPackage :
      CombinedEstimatePackage
    blockerLedger :
      ExactBlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List EstimateLane
    receiptRecorded :
      Bool
    localJacobianPartitionPackageRecordedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    evidenceLedger :
      List String

open YMSprint113LocalJacobianPartitionEstimateReceipt public

canonicalImportedMapCandidateReceipts : ImportedMapCandidateReceipts
canonicalImportedMapCandidateReceipts =
  mkImportedMapCandidateReceipts
    Uniform112.canonicalReceipt
    Interp112.canonicalReceipt
    Sampling112.canonicalReceipt
    Maps111.canonicalReceipt
    Uniform112.canonicalReceiptClayYangMillsPromotedIsFalse
    Interp112.canonicalReceiptClayYangMillsPromotedIsFalse
    Sampling112.canonicalClayYangMillsPromotedIsFalse
    refl

canonicalConcreteConstantLedger : ConcreteConstantLedger
canonicalConcreteConstantLedger =
  mkConcreteConstantLedger
    16
    8
    4
    32
    12
    3
    5
    15
    7
    645120
    combinedConstantText
    true
    concrete-constant-ledger

canonicalLocalJacobianLedgerEntry : LocalJacobianLedgerEntry
canonicalLocalJacobianLedgerEntry =
  mkLocalJacobianLedgerEntry
    local-jacobian-lane
    local-jacobian-kind
    localJacobianEstimateText
    "Q_i(a)"
    "E_a and P_a candidates from Sprint112"
    "J_i(a)"
    "rho_i(a)"
    "0 < a <= a0"
    canonicalConcreteConstantLedger
    localJacobianLedgerRecorded
    localJacobianEstimateProvedHere
    refl
    recorded-inhabited

canonicalChartVolumeDensityComparison : ChartVolumeDensityComparison
canonicalChartVolumeDensityComparison =
  mkChartVolumeDensityComparison
    chart-volume-density-lane
    chart-volume-density-kind
    chartVolumeDensityComparisonText
    "V_i(a)"
    "rho_i(a)"
    "referenceCellMass_i(a)"
    32
    true
    true
    chartVolumeDensityComparisonRecorded
    chartVolumeDensityTheoremProvedHere
    refl
    recorded-inhabited

canonicalFiniteOverlapSummation : FiniteOverlapSummation
canonicalFiniteOverlapSummation =
  mkFiniteOverlapSummation
    finite-overlap-summation-lane
    finite-overlap-kind
    finiteOverlapSummationText
    "chi_i"
    "B_i"
    "sum_i B_i"
    12
    finiteOverlapSummationRecorded
    true
    "If every point belongs to at most M=12 chart supports, then the ledger records sum_i chi_i(x) B_i <= 12 * sum_i B_i for nonnegative local estimate entries."
    finiteOverlapSummationTheoremProvedHere
    refl
    finite-overlap-recorded

canonicalDerivativeLossAccount : DerivativeLossAccount
canonicalDerivativeLossAccount =
  mkDerivativeLossAccount
    derivative-loss-lane
    derivative-loss-kind
    derivativeLossAccountingText
    "chi_i"
    2
    3
    5
    15
    true
    true
    true
    derivativeLossAccountingRecorded
    derivativeLossAbsorptionProvedHere
    refl
    derivative-loss-recorded

canonicalQuotientCompatibilityEstimate : QuotientCompatibilityEstimate
canonicalQuotientCompatibilityEstimate =
  mkQuotientCompatibilityEstimate
    quotient-compatibility-lane
    quotient-comparison-kind
    "Quotient compatibility estimate package: the local chart comparison is recorded with C_quot=7 for descent from representative-level estimates to H_a,phys / gauge and H_phys physical-sector norms."
    "||-||_a,quot"
    "||-||_H_phys"
    7
    true
    true
    true
    mapCandidateProvenanceRecorded
    uniformNormBoundClosedHere
    refl
    analytic-proof-required

canonicalCombinedEstimatePackage : CombinedEstimatePackage
canonicalCombinedEstimatePackage =
  mkCombinedEstimatePackage
    combined-ledger-lane
    combined-package-kind
    combinedConstantText
    canonicalLocalJacobianLedgerEntry
    canonicalChartVolumeDensityComparison
    canonicalFiniteOverlapSummation
    canonicalDerivativeLossAccount
    canonicalQuotientCompatibilityEstimate
    645120
    true
    uniformNormBoundClosedHere
    refl
    concrete-constant-ledger

canonicalBlockerEntries : List BlockerLedgerEntry
canonicalBlockerEntries =
  mkBlockerLedgerEntry
    jacobian-blocker
    local-jacobian-lane
    jacobianBlockerText
    true
    true
    localJacobianEstimateProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    chart-volume-density-blocker
    chart-volume-density-lane
    chartVolumeDensityBlockerText
    true
    true
    chartVolumeDensityTheoremProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    finite-overlap-blocker
    finite-overlap-summation-lane
    finiteOverlapBlockerText
    true
    true
    finiteOverlapSummationTheoremProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    derivative-loss-blocker
    derivative-loss-lane
    derivativeLossBlockerText
    true
    true
    derivativeLossAbsorptionProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    quotient-compatibility-blocker
    quotient-compatibility-lane
    quotientCompatibilityBlockerText
    true
    true
    uniformNormBoundClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    uniform-reduction-blocker
    combined-ledger-lane
    uniformReductionBlockerText
    true
    true
    uniformNormBoundClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    nonpromotion-blocker
    receipt-lane
    nonPromotionBoundaryText
    true
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion
  ∷ []

canonicalExactBlockerLedger : ExactBlockerLedger
canonicalExactBlockerLedger =
  mkExactBlockerLedger
    blocker-lane
    canonicalBlockerEntries
    jacobianBlockerText
    chartVolumeDensityBlockerText
    finiteOverlapBlockerText
    derivativeLossBlockerText
    quotientCompatibilityBlockerText
    uniformReductionBlockerText
    true
    true
    exact-blocker-recorded

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    "Sprint113 target: supply local Jacobian, chart-volume/density, finite-overlap, derivative-loss, and quotient-compatibility estimates sufficient to discharge the Sprint112 uniform norm bound reduction."
    nonPromotionBoundaryText
    localJacobianEstimateProvedHere
    refl
    partitionMultiplicityEstimateProvedHere
    refl
    finiteOverlapSummationTheoremProvedHere
    refl
    chartVolumeDensityTheoremProvedHere
    refl
    derivativeLossAbsorptionProvedHere
    refl
    uniformNormBoundClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  admissibleWindowText
  ∷ localJacobianEstimateText
  ∷ chartVolumeDensityComparisonText
  ∷ finiteOverlapSummationText
  ∷ derivativeLossAccountingText
  ∷ combinedConstantText
  ∷ jacobianBlockerText
  ∷ chartVolumeDensityBlockerText
  ∷ finiteOverlapBlockerText
  ∷ derivativeLossBlockerText
  ∷ quotientCompatibilityBlockerText
  ∷ uniformReductionBlockerText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint113LocalJacobianPartitionEstimateReceipt :
  YMSprint113LocalJacobianPartitionEstimateReceipt
canonicalYMSprint113LocalJacobianPartitionEstimateReceipt =
  mkYMSprint113LocalJacobianPartitionEstimateReceipt
    sprintNumber
    modulePath
    canonicalImportedMapCandidateReceipts
    canonicalConcreteConstantLedger
    canonicalLocalJacobianLedgerEntry
    canonicalChartVolumeDensityComparison
    canonicalFiniteOverlapSummation
    canonicalDerivativeLossAccount
    canonicalQuotientCompatibilityEstimate
    canonicalCombinedEstimatePackage
    canonicalExactBlockerLedger
    canonicalTheoremBoundary
    canonicalEstimateLanes
    true
    localJacobianPartitionPackageRecorded
    clayYangMillsPromoted
    refl
    canonicalEvidenceLedger

canonicalReceipt : YMSprint113LocalJacobianPartitionEstimateReceipt
canonicalReceipt =
  canonicalYMSprint113LocalJacobianPartitionEstimateReceipt

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptLocalJacobianEstimateProvedHereIsFalse :
  TheoremBoundary.localJacobianEstimateProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptLocalJacobianEstimateProvedHereIsFalse =
  refl

canonicalReceiptPartitionMultiplicityEstimateProvedHereIsFalse :
  TheoremBoundary.partitionMultiplicityEstimateProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptPartitionMultiplicityEstimateProvedHereIsFalse =
  refl

canonicalReceiptFiniteOverlapSummationTheoremProvedHereIsFalse :
  TheoremBoundary.finiteOverlapSummationTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptFiniteOverlapSummationTheoremProvedHereIsFalse =
  refl

canonicalReceiptChartVolumeDensityTheoremProvedHereIsFalse :
  TheoremBoundary.chartVolumeDensityTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptChartVolumeDensityTheoremProvedHereIsFalse =
  refl

canonicalReceiptDerivativeLossAbsorptionProvedHereIsFalse :
  TheoremBoundary.derivativeLossAbsorptionProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptDerivativeLossAbsorptionProvedHereIsFalse =
  refl

canonicalReceiptUniformNormBoundClosedHereIsFalse :
  TheoremBoundary.uniformNormBoundClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptUniformNormBoundClosedHereIsFalse =
  refl

canonicalReceiptCombinedConstant : Nat
canonicalReceiptCombinedConstant =
  CombinedEstimatePackage.combinedConstant (combinedPackage canonicalReceipt)

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
