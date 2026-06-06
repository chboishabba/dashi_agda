module DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111
import DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction
  as Uniform112

------------------------------------------------------------------------
-- Sprint114 common-carrier estimate closure assembly.
--
-- This module assembles the route from the Sprint111 common-carrier
-- construction criteria and Sprint112 uniform norm reduction to the Sprint113
-- estimate package surface.  Sprint113 evidence is referenced by source path
-- strings to avoid racing sibling Sprint114/Sprint113 workers.  The receipt is
-- inhabited and fail-closed: it records closure criteria, constants, residual
-- requirements, inverse/projection requirements, weak/recovery feed-through
-- requirements, exact blockers, and the transfer lower-bound transfer route.
-- It proves no analytic estimate theorem, no transfer lower-bound theorem, no
-- continuum gap theorem, and no Clay Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 114

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint114CommonCarrierEstimateClosureAssembly.agda"

sprint111CommonCarrierSourcePath : String
sprint111CommonCarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint111CommonCarrierConstructionAssembly.agda"

sprint112UniformNormSourcePath : String
sprint112UniformNormSourcePath =
  "DASHI/Physics/Closure/YMSprint112UniformNormBoundReduction.agda"

sprint113LocalJacobianPartitionSourcePath : String
sprint113LocalJacobianPartitionSourcePath =
  "DASHI/Physics/Closure/YMSprint113LocalJacobianPartitionEstimate.agda"

sprint113QuadratureResidualSourcePath : String
sprint113QuadratureResidualSourcePath =
  "DASHI/Physics/Closure/YMSprint113QuadratureResidualEstimate.agda"

sprint113InverseProjectionSourcePath : String
sprint113InverseProjectionSourcePath =
  "DASHI/Physics/Closure/YMSprint113InverseProjectionResidualAssembly.agda"

sprint113GaugeCovarianceSourcePath : String
sprint113GaugeCovarianceSourcePath =
  "DASHI/Physics/Closure/YMSprint113GaugeCovarianceLocalSectionEstimate.agda"

sprint113QuotientNormSourcePath : String
sprint113QuotientNormSourcePath =
  "DASHI/Physics/Closure/YMSprint113QuotientNormComparisonEstimate.agda"

assemblyRecorded : Bool
assemblyRecorded = true

gaugeQuotientClosureCriterionRecorded : Bool
gaugeQuotientClosureCriterionRecorded = true

uniformNormConstantAssemblyRecorded : Bool
uniformNormConstantAssemblyRecorded = true

quadratureResidualClosureRecorded : Bool
quadratureResidualClosureRecorded = true

inverseProjectionClosureRecorded : Bool
inverseProjectionClosureRecorded = true

weakRecoveryFeedThroughRequirementsRecorded : Bool
weakRecoveryFeedThroughRequirementsRecorded = true

exactBlockersRecorded : Bool
exactBlockersRecorded = true

failClosedTransferRouteRecorded : Bool
failClosedTransferRouteRecorded = true

gaugeQuotientClosureClosedHere : Bool
gaugeQuotientClosureClosedHere = false

uniformNormConstantClosedHere : Bool
uniformNormConstantClosedHere = false

quadratureResidualClosedHere : Bool
quadratureResidualClosedHere = false

inverseProjectionClosedHere : Bool
inverseProjectionClosedHere = false

weakCompactnessFedHere : Bool
weakCompactnessFedHere = false

recoveryLimsupFedHere : Bool
recoveryLimsupFedHere = false

commonCarrierEstimateClosureClosedHere : Bool
commonCarrierEstimateClosureClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTransferredHere : Bool
transferLowerBoundTransferredHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

importedSprint111AssemblyRecorded : Bool
importedSprint111AssemblyRecorded =
  Carrier111.sprint111AssemblyRecorded

importedSprint111CommonCarrierClosed : Bool
importedSprint111CommonCarrierClosed =
  Carrier111.commonCarrierConstructionClosedHere

importedSprint111TransferLowerBoundProved : Bool
importedSprint111TransferLowerBoundProved =
  Carrier111.transferLowerBoundTheoremProvedHere

importedSprint112ReductionRecorded : Bool
importedSprint112ReductionRecorded =
  Uniform112.uniformNormBoundReductionRecorded

importedSprint112NormEquivalenceClosed : Bool
importedSprint112NormEquivalenceClosed =
  Uniform112.normEquivalenceTheoremProvedHere

importedSprint112WeakCompactnessFed : Bool
importedSprint112WeakCompactnessFed =
  Uniform112.weakCompactnessFedHere

gaugeQuotientClosureCriterionText : String
gaugeQuotientClosureCriterionText =
  "Gauge quotient closure criterion: common-carrier estimate closure requires finite representative independence, continuum physical projection compatibility, quotient norm comparison, local section gauge covariance, and vacuum/non-vacuum sector leakage exclusion on the same E_a/P_a convention."

uniformNormConstantAssemblyText : String
uniformNormConstantAssemblyText =
  "Uniform norm constant assembly: consume the Sprint113 constant ledger C_local=16, C_Vrho=32, M=12, L_total=15, C_quot=7, recording C_package=645120 as the concrete bookkeeping constant needed by the Sprint112 upper/lower norm reductions."

quadratureResidualClosureText : String
quadratureResidualClosureText =
  "Quadrature residual closure requirement: cell quadrature, smoothing, holonomy sampling, and renormalized inner-product residuals must vanish uniformly on the Sprint112 admissible window before adjointness or approximate inverse closure can be consumed."

inverseProjectionClosureText : String
inverseProjectionClosureText =
  "Inverse/projection closure requirement: left E_a o P_a residuals, right P_a o E_a residuals, physical projection commutators, quotient descent, and sector stability must close together before the Sprint111 common carrier can be treated as constructed."

weakRecoveryFeedThroughRequirementsText : String
weakRecoveryFeedThroughRequirementsText =
  "Weak/recovery feed-through requirements: after common-carrier estimates close, the same carrier and normalization must feed Sprint110 weak compactness, closed-form lower semicontinuity, recovery strong convergence, and recovery energy limsup without relabelling carrier or sector data."

failClosedTransferLowerBoundRouteText : String
failClosedTransferLowerBoundRouteText =
  "Fail-closed route to transfer lower-bound: only after gauge quotient closure, uniform norm constants, quadrature residual closure, inverse/projection closure, weak compactness feed-through, and recovery limsup feed-through are all proved can the transfer lower-bound theorem be re-opened; this module records the route and keeps transferLowerBoundTransferredHere=false."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint114 common-carrier estimate closure assembly records requirements and blockers only; it does not close the analytic estimate package, transfer lower-bound theorem, continuum mass gap, or Clay Yang-Mills promotion."

gaugeQuotientBlockerText : String
gaugeQuotientBlockerText =
  "Exact blocker A: no proof in this module establishes representative independence, physical projection compatibility, quotient norm comparison, local section gauge covariance, and sector leakage exclusion as one closure criterion."

uniformNormConstantBlockerText : String
uniformNormConstantBlockerText =
  "Exact blocker B: the constant C_package=645120 is recorded as arithmetic bookkeeping, but no theorem proves it is a valid cutoff-uniform upper/lower norm constant."

quadratureResidualBlockerText : String
quadratureResidualBlockerText =
  "Exact blocker C: no proof shows the cell, smoothing, holonomy, and renormalization residuals vanish uniformly enough to close the Sprint112 adjointness residual."

inverseProjectionBlockerText : String
inverseProjectionBlockerText =
  "Exact blocker D: no proof closes left inverse, right inverse, projection commutator, quotient descent, and sector stability residuals together."

weakRecoveryFeedThroughBlockerText : String
weakRecoveryFeedThroughBlockerText =
  "Exact blocker E: no proof feeds the assembled common carrier through weak compactness, lower semicontinuity, recovery strong convergence, and recovery energy limsup without changing carriers."

transferLowerBoundBlockerText : String
transferLowerBoundBlockerText =
  "Exact blocker F: the transfer lower-bound theorem cannot be transferred because the common-carrier estimate closure criteria remain open."

clayPromotionBlockerText : String
clayPromotionBlockerText =
  "Exact blocker G: Clay Yang-Mills promotion remains false because the transfer lower-bound theorem and continuum gap theorem are not proved here."

data ClosureLane : Set where
  sprint111-common-carrier-input-lane :
    ClosureLane
  sprint112-uniform-norm-input-lane :
    ClosureLane
  gauge-quotient-closure-lane :
    ClosureLane
  uniform-norm-constant-lane :
    ClosureLane
  quadrature-residual-closure-lane :
    ClosureLane
  inverse-projection-closure-lane :
    ClosureLane
  weak-recovery-feed-through-lane :
    ClosureLane
  transfer-lower-bound-route-lane :
    ClosureLane
  exact-blocker-lane :
    ClosureLane
  receipt-lane :
    ClosureLane

data ClosureStatus : Set where
  imported-stable-input :
    ClosureStatus
  source-path-recorded :
    ClosureStatus
  closure-criterion-recorded :
    ClosureStatus
  concrete-constant-recorded :
    ClosureStatus
  residual-closure-required :
    ClosureStatus
  inverse-projection-required :
    ClosureStatus
  feed-through-required :
    ClosureStatus
  exact-blocker-recorded :
    ClosureStatus
  transfer-route-fail-closed :
    ClosureStatus
  fail-closed-nonpromotion :
    ClosureStatus

data BlockerKind : Set where
  gauge-quotient-blocker :
    BlockerKind
  uniform-norm-constant-blocker :
    BlockerKind
  quadrature-residual-blocker :
    BlockerKind
  inverse-projection-blocker :
    BlockerKind
  weak-recovery-feed-through-blocker :
    BlockerKind
  transfer-lower-bound-blocker :
    BlockerKind
  clay-promotion-blocker :
    BlockerKind

canonicalClosureLanes : List ClosureLane
canonicalClosureLanes =
  sprint111-common-carrier-input-lane
  ∷ sprint112-uniform-norm-input-lane
  ∷ gauge-quotient-closure-lane
  ∷ uniform-norm-constant-lane
  ∷ quadrature-residual-closure-lane
  ∷ inverse-projection-closure-lane
  ∷ weak-recovery-feed-through-lane
  ∷ transfer-lower-bound-route-lane
  ∷ exact-blocker-lane
  ∷ receipt-lane
  ∷ []

record StableInputs : Setω where
  constructor mkStableInputs
  field
    sprint111CommonCarrierReceipt :
      Carrier111.AssemblyReceipt
    sprint112UniformNormReceipt :
      Uniform112.YMSprint112UniformNormBoundReductionReceipt
    sprint111SourcePath :
      String
    sprint112SourcePath :
      String
    sprint111AssemblyRecordedHere :
      Bool
    sprint112ReductionRecordedHere :
      Bool
    sprint111CommonCarrierClosed :
      Bool
    sprint112NormEquivalenceClosed :
      Bool
    sprint111TransferLowerBoundProved :
      Bool
    sprint112WeakCompactnessFed :
      Bool
    sprint111CommonCarrierClosedIsFalse :
      sprint111CommonCarrierClosed ≡ false
    sprint112NormEquivalenceClosedIsFalse :
      sprint112NormEquivalenceClosed ≡ false
    sprint111TransferLowerBoundProvedIsFalse :
      sprint111TransferLowerBoundProved ≡ false
    sprint112WeakCompactnessFedIsFalse :
      sprint112WeakCompactnessFed ≡ false
    sprint111ClayPromotionFalse :
      Carrier111.clayYangMillsPromoted ≡ false
    sprint112ClayPromotionFalse :
      Uniform112.clayYangMillsPromotedHere
        Uniform112.canonicalReceipt ≡ false

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    localJacobianPartitionPath :
      String
    quadratureResidualPath :
      String
    inverseProjectionPath :
      String
    gaugeCovariancePath :
      String
    quotientNormPath :
      String
    usesSourcePathsToAvoidSiblingRace :
      Bool
    status :
      ClosureStatus

record GaugeQuotientClosureCriterion : Set where
  constructor mkGaugeQuotientClosureCriterion
  field
    lane :
      ClosureLane
    statement :
      String
    finiteRepresentativeIndependenceRequired :
      Bool
    continuumPhysicalProjectionCompatibilityRequired :
      Bool
    quotientNormComparisonRequired :
      Bool
    localSectionGaugeCovarianceRequired :
      Bool
    sectorLeakageExclusionRequired :
      Bool
    recordedHere :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ClosureStatus

record UniformNormConstantAssembly : Set where
  constructor mkUniformNormConstantAssembly
  field
    lane :
      ClosureLane
    statement :
      String
    chartJacobianConstant :
      Nat
    chartVolumeDensityConstant :
      Nat
    overlapMultiplicity :
      Nat
    derivativeLossConstant :
      Nat
    quotientComparisonConstant :
      Nat
    packageConstant :
      Nat
    constantLedgerConcrete :
      Bool
    feedsSprint112UpperReduction :
      Bool
    feedsSprint112LowerReduction :
      Bool
    provedUniformHere :
      Bool
    provedUniformHereIsFalse :
      provedUniformHere ≡ false
    status :
      ClosureStatus

record QuadratureResidualClosure : Set where
  constructor mkQuadratureResidualClosure
  field
    lane :
      ClosureLane
    statement :
      String
    cellQuadratureRequired :
      Bool
    smoothingRequired :
      Bool
    holonomySamplingRequired :
      Bool
    renormalizedInnerProductRequired :
      Bool
    adjointnessResidualTargetRequired :
      Bool
    recordedHere :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ClosureStatus

record InverseProjectionClosure : Set where
  constructor mkInverseProjectionClosure
  field
    lane :
      ClosureLane
    statement :
      String
    leftInverseRequired :
      Bool
    rightInverseRequired :
      Bool
    projectionCommutatorRequired :
      Bool
    quotientDescentRequired :
      Bool
    physicalSectorStabilityRequired :
      Bool
    vacuumSectorStabilityRequired :
      Bool
    recordedHere :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ClosureStatus

record WeakRecoveryFeedThroughRequirements : Set where
  constructor mkWeakRecoveryFeedThroughRequirements
  field
    lane :
      ClosureLane
    statement :
      String
    weakCompactnessRequired :
      Bool
    lowerSemicontinuityRequired :
      Bool
    recoveryStrongConvergenceRequired :
      Bool
    recoveryEnergyLimsupRequired :
      Bool
    sameCarrierRequired :
      Bool
    sameNormalizationRequired :
      Bool
    recordedHere :
      Bool
    weakCompactnessFed :
      Bool
    recoveryLimsupFed :
      Bool
    weakCompactnessFedIsFalse :
      weakCompactnessFed ≡ false
    recoveryLimsupFedIsFalse :
      recoveryLimsupFed ≡ false
    status :
      ClosureStatus

record BlockerReceipt : Set where
  constructor mkBlockerReceipt
  field
    blocker :
      BlockerKind
    lane :
      ClosureLane
    statement :
      String
    sourcePath :
      String
    blocksEstimateClosure :
      Bool
    blocksTransferLowerBound :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ClosureStatus

record ExactBlockerLedger : Set where
  constructor mkExactBlockerLedger
  field
    lane :
      ClosureLane
    gaugeQuotientBlocker :
      String
    uniformNormConstantBlocker :
      String
    quadratureResidualBlocker :
      String
    inverseProjectionBlocker :
      String
    weakRecoveryFeedThroughBlocker :
      String
    transferLowerBoundBlocker :
      String
    clayPromotionBlocker :
      String
    blockerReceipts :
      List BlockerReceipt
    blockerTexts :
      List String
    allBlockersExact :
      Bool
    theoremStillOpen :
      Bool
    status :
      ClosureStatus

record TransferLowerBoundFailClosedRoute : Set where
  constructor mkTransferLowerBoundFailClosedRoute
  field
    lane :
      ClosureLane
    routeStatement :
      String
    needsGaugeQuotientClosure :
      Bool
    needsUniformNormConstants :
      Bool
    needsQuadratureResidualClosure :
      Bool
    needsInverseProjectionClosure :
      Bool
    needsWeakCompactnessFeed :
      Bool
    needsRecoveryLimsupFeed :
      Bool
    routeRecorded :
      Bool
    readyHere :
      Bool
    transferredHere :
      Bool
    readyHereIsFalse :
      readyHere ≡ false
    transferredHereIsFalse :
      transferredHere ≡ false
    status :
      ClosureStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    gaugeQuotientClosureClosedHereFlag :
      Bool
    gaugeQuotientClosureClosedHereIsFalse :
      gaugeQuotientClosureClosedHereFlag ≡ false
    uniformNormConstantClosedHereFlag :
      Bool
    uniformNormConstantClosedHereIsFalse :
      uniformNormConstantClosedHereFlag ≡ false
    quadratureResidualClosedHereFlag :
      Bool
    quadratureResidualClosedHereIsFalse :
      quadratureResidualClosedHereFlag ≡ false
    inverseProjectionClosedHereFlag :
      Bool
    inverseProjectionClosedHereIsFalse :
      inverseProjectionClosedHereFlag ≡ false
    weakCompactnessFedHereFlag :
      Bool
    weakCompactnessFedHereIsFalse :
      weakCompactnessFedHereFlag ≡ false
    recoveryLimsupFedHereFlag :
      Bool
    recoveryLimsupFedHereIsFalse :
      recoveryLimsupFedHereFlag ≡ false
    commonCarrierEstimateClosureClosedHereFlag :
      Bool
    commonCarrierEstimateClosureClosedHereIsFalse :
      commonCarrierEstimateClosureClosedHereFlag ≡ false
    transferLowerBoundTransferredHereFlag :
      Bool
    transferLowerBoundTransferredHereIsFalse :
      transferLowerBoundTransferredHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ClosureStatus

record YMSprint114CommonCarrierEstimateClosureAssemblyReceipt : Setω where
  constructor mkYMSprint114CommonCarrierEstimateClosureAssemblyReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    stableInputs :
      StableInputs
    sourcePaths :
      SourcePathLedger
    gaugeQuotientClosure :
      GaugeQuotientClosureCriterion
    uniformNormConstants :
      UniformNormConstantAssembly
    quadratureResidualClosure :
      QuadratureResidualClosure
    inverseProjectionClosure :
      InverseProjectionClosure
    weakRecoveryFeedThrough :
      WeakRecoveryFeedThroughRequirements
    blockers :
      ExactBlockerLedger
    transferRoute :
      TransferLowerBoundFailClosedRoute
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ClosureLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint114CommonCarrierEstimateClosureAssemblyReceipt public

canonicalStableInputs : StableInputs
canonicalStableInputs =
  mkStableInputs
    Carrier111.canonicalAssemblyReceipt
    Uniform112.canonicalReceipt
    sprint111CommonCarrierSourcePath
    sprint112UniformNormSourcePath
    importedSprint111AssemblyRecorded
    importedSprint112ReductionRecorded
    importedSprint111CommonCarrierClosed
    importedSprint112NormEquivalenceClosed
    importedSprint111TransferLowerBoundProved
    importedSprint112WeakCompactnessFed
    refl
    refl
    refl
    refl
    Carrier111.clayYangMillsPromotedIsFalse
    Uniform112.canonicalReceiptClayYangMillsPromotedIsFalse

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    sprint113LocalJacobianPartitionSourcePath
    sprint113QuadratureResidualSourcePath
    sprint113InverseProjectionSourcePath
    sprint113GaugeCovarianceSourcePath
    sprint113QuotientNormSourcePath
    true
    source-path-recorded

canonicalGaugeQuotientClosureCriterion :
  GaugeQuotientClosureCriterion
canonicalGaugeQuotientClosureCriterion =
  mkGaugeQuotientClosureCriterion
    gauge-quotient-closure-lane
    gaugeQuotientClosureCriterionText
    true
    true
    true
    true
    true
    gaugeQuotientClosureCriterionRecorded
    gaugeQuotientClosureClosedHere
    refl
    closure-criterion-recorded

canonicalUniformNormConstantAssembly :
  UniformNormConstantAssembly
canonicalUniformNormConstantAssembly =
  mkUniformNormConstantAssembly
    uniform-norm-constant-lane
    uniformNormConstantAssemblyText
    16
    32
    12
    15
    7
    645120
    true
    true
    true
    uniformNormConstantClosedHere
    refl
    concrete-constant-recorded

canonicalQuadratureResidualClosure :
  QuadratureResidualClosure
canonicalQuadratureResidualClosure =
  mkQuadratureResidualClosure
    quadrature-residual-closure-lane
    quadratureResidualClosureText
    true
    true
    true
    true
    true
    quadratureResidualClosureRecorded
    quadratureResidualClosedHere
    refl
    residual-closure-required

canonicalInverseProjectionClosure :
  InverseProjectionClosure
canonicalInverseProjectionClosure =
  mkInverseProjectionClosure
    inverse-projection-closure-lane
    inverseProjectionClosureText
    true
    true
    true
    true
    true
    true
    inverseProjectionClosureRecorded
    inverseProjectionClosedHere
    refl
    inverse-projection-required

canonicalWeakRecoveryFeedThroughRequirements :
  WeakRecoveryFeedThroughRequirements
canonicalWeakRecoveryFeedThroughRequirements =
  mkWeakRecoveryFeedThroughRequirements
    weak-recovery-feed-through-lane
    weakRecoveryFeedThroughRequirementsText
    true
    true
    true
    true
    true
    true
    weakRecoveryFeedThroughRequirementsRecorded
    weakCompactnessFedHere
    recoveryLimsupFedHere
    refl
    refl
    feed-through-required

canonicalBlockerReceipts : List BlockerReceipt
canonicalBlockerReceipts =
  mkBlockerReceipt
    gauge-quotient-blocker
    gauge-quotient-closure-lane
    gaugeQuotientBlockerText
    sprint113GaugeCovarianceSourcePath
    true
    true
    gaugeQuotientClosureClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    uniform-norm-constant-blocker
    uniform-norm-constant-lane
    uniformNormConstantBlockerText
    sprint113LocalJacobianPartitionSourcePath
    true
    true
    uniformNormConstantClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    quadrature-residual-blocker
    quadrature-residual-closure-lane
    quadratureResidualBlockerText
    sprint113QuadratureResidualSourcePath
    true
    true
    quadratureResidualClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    inverse-projection-blocker
    inverse-projection-closure-lane
    inverseProjectionBlockerText
    sprint113InverseProjectionSourcePath
    true
    true
    inverseProjectionClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    weak-recovery-feed-through-blocker
    weak-recovery-feed-through-lane
    weakRecoveryFeedThroughBlockerText
    sprint111CommonCarrierSourcePath
    true
    true
    weakCompactnessFedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    transfer-lower-bound-blocker
    transfer-lower-bound-route-lane
    transferLowerBoundBlockerText
    sprint111CommonCarrierSourcePath
    true
    true
    transferLowerBoundTransferredHere
    refl
    transfer-route-fail-closed
  ∷ mkBlockerReceipt
    clay-promotion-blocker
    receipt-lane
    clayPromotionBlockerText
    modulePath
    true
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion
  ∷ []

canonicalExactBlockerLedger : ExactBlockerLedger
canonicalExactBlockerLedger =
  mkExactBlockerLedger
    exact-blocker-lane
    gaugeQuotientBlockerText
    uniformNormConstantBlockerText
    quadratureResidualBlockerText
    inverseProjectionBlockerText
    weakRecoveryFeedThroughBlockerText
    transferLowerBoundBlockerText
    clayPromotionBlockerText
    canonicalBlockerReceipts
    (gaugeQuotientBlockerText
     ∷ uniformNormConstantBlockerText
     ∷ quadratureResidualBlockerText
     ∷ inverseProjectionBlockerText
     ∷ weakRecoveryFeedThroughBlockerText
     ∷ transferLowerBoundBlockerText
     ∷ clayPromotionBlockerText
     ∷ [])
    true
    true
    exact-blocker-recorded

canonicalTransferLowerBoundFailClosedRoute :
  TransferLowerBoundFailClosedRoute
canonicalTransferLowerBoundFailClosedRoute =
  mkTransferLowerBoundFailClosedRoute
    transfer-lower-bound-route-lane
    failClosedTransferLowerBoundRouteText
    true
    true
    true
    true
    true
    true
    failClosedTransferRouteRecorded
    transferLowerBoundReadyHere
    transferLowerBoundTransferredHere
    refl
    refl
    transfer-route-fail-closed

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    gaugeQuotientClosureClosedHere
    refl
    uniformNormConstantClosedHere
    refl
    quadratureResidualClosedHere
    refl
    inverseProjectionClosedHere
    refl
    weakCompactnessFedHere
    refl
    recoveryLimsupFedHere
    refl
    commonCarrierEstimateClosureClosedHere
    refl
    transferLowerBoundTransferredHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  gaugeQuotientClosureCriterionText
  ∷ uniformNormConstantAssemblyText
  ∷ quadratureResidualClosureText
  ∷ inverseProjectionClosureText
  ∷ weakRecoveryFeedThroughRequirementsText
  ∷ failClosedTransferLowerBoundRouteText
  ∷ gaugeQuotientBlockerText
  ∷ uniformNormConstantBlockerText
  ∷ quadratureResidualBlockerText
  ∷ inverseProjectionBlockerText
  ∷ weakRecoveryFeedThroughBlockerText
  ∷ transferLowerBoundBlockerText
  ∷ clayPromotionBlockerText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint114CommonCarrierEstimateClosureAssemblyReceipt :
  YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
canonicalYMSprint114CommonCarrierEstimateClosureAssemblyReceipt =
  mkYMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    sprintNumber
    modulePath
    canonicalStableInputs
    canonicalSourcePathLedger
    canonicalGaugeQuotientClosureCriterion
    canonicalUniformNormConstantAssembly
    canonicalQuadratureResidualClosure
    canonicalInverseProjectionClosure
    canonicalWeakRecoveryFeedThroughRequirements
    canonicalExactBlockerLedger
    canonicalTransferLowerBoundFailClosedRoute
    canonicalTheoremBoundary
    canonicalClosureLanes
    canonicalEvidenceLedger
    assemblyRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
canonicalReceipt =
  canonicalYMSprint114CommonCarrierEstimateClosureAssemblyReceipt

canonicalGaugeQuotientClosureClosedHereIsFalse :
  TheoremBoundary.gaugeQuotientClosureClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalGaugeQuotientClosureClosedHereIsFalse =
  refl

canonicalUniformNormConstantClosedHereIsFalse :
  TheoremBoundary.uniformNormConstantClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalUniformNormConstantClosedHereIsFalse =
  refl

canonicalQuadratureResidualClosedHereIsFalse :
  TheoremBoundary.quadratureResidualClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalQuadratureResidualClosedHereIsFalse =
  refl

canonicalInverseProjectionClosedHereIsFalse :
  TheoremBoundary.inverseProjectionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalInverseProjectionClosedHereIsFalse =
  refl

canonicalWeakCompactnessFedHereIsFalse :
  TheoremBoundary.weakCompactnessFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalWeakCompactnessFedHereIsFalse =
  refl

canonicalRecoveryLimsupFedHereIsFalse :
  TheoremBoundary.recoveryLimsupFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalRecoveryLimsupFedHereIsFalse =
  refl

canonicalCommonCarrierEstimateClosureClosedHereIsFalse :
  TheoremBoundary.commonCarrierEstimateClosureClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCommonCarrierEstimateClosureClosedHereIsFalse =
  refl

canonicalTransferLowerBoundTransferredHereIsFalse :
  TheoremBoundary.transferLowerBoundTransferredHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalTransferLowerBoundTransferredHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalTransferRoute :
  TransferLowerBoundFailClosedRoute
canonicalTransferRoute =
  transferRoute canonicalReceipt

canonicalBlockers :
  ExactBlockerLedger
canonicalBlockers =
  blockers canonicalReceipt

canonicalSourcePaths :
  SourcePathLedger
canonicalSourcePaths =
  sourcePaths canonicalReceipt

canonicalPackageConstant : Nat
canonicalPackageConstant =
  UniformNormConstantAssembly.packageConstant
    (uniformNormConstants canonicalReceipt)
