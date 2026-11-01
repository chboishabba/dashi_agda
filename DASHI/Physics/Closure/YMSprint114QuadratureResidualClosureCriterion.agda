module DASHI.Physics.Closure.YMSprint114QuadratureResidualClosureCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112AdjointnessApproxInverseReduction
  as Reduction112
import DASHI.Physics.Closure.YMSprint113QuadratureResidualEstimate
  as Estimate113

------------------------------------------------------------------------
-- Sprint114 quadrature residual closure criterion.
--
-- This module assembles the Sprint113 residual estimate ledger into a
-- precise closure criterion for the Sprint112 adjointness residual.  The
-- criterion is satisfied only when the cell quadrature, smoothing,
-- holonomy sampling, renormalized inner-product convergence, and vanishing
-- rate ledger are supplied together.
--
-- Approximate inverse closure remains a separate lane.  It is not inferred
-- from adjointness residual closure unless an explicit approximate-inverse
-- supply is provided.

sprintNumber : Nat
sprintNumber = 114

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint114QuadratureResidualClosureCriterion.agda"

estimate113Path : String
estimate113Path =
  "DASHI/Physics/Closure/YMSprint113QuadratureResidualEstimate.agda"

reduction112Path : String
reduction112Path =
  "DASHI/Physics/Closure/YMSprint112AdjointnessApproxInverseReduction.agda"

quadratureResidualClosureCriterionRecorded : Bool
quadratureResidualClosureCriterionRecorded = true

suppliedEvidenceCriterionRecorded : Bool
suppliedEvidenceCriterionRecorded = true

vanishingRateLedgerCriterionRecorded : Bool
vanishingRateLedgerCriterionRecorded = true

adjointnessResidualClosureSatisfiedWhenSupplied : Bool
adjointnessResidualClosureSatisfiedWhenSupplied = true

approximateInverseKeptSeparate : Bool
approximateInverseKeptSeparate = true

canonicalSuppliesAvailableHere : Bool
canonicalSuppliesAvailableHere = false

cellQuadratureConvergenceProvedHere : Bool
cellQuadratureConvergenceProvedHere = false

smoothingApproximationConvergenceProvedHere : Bool
smoothingApproximationConvergenceProvedHere = false

holonomySamplingConvergenceProvedHere : Bool
holonomySamplingConvergenceProvedHere = false

renormalizedInnerProductConvergenceProvedHere : Bool
renormalizedInnerProductConvergenceProvedHere = false

vanishingRateLedgerProvedHere : Bool
vanishingRateLedgerProvedHere = false

adjointnessResidualClosureProvedHere : Bool
adjointnessResidualClosureProvedHere = false

approximateInverseClosureProvedHere : Bool
approximateInverseClosureProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

closureCriterionText : String
closureCriterionText =
  "Sprint114 criterion: if cell quadrature convergence, smoothing approximation convergence, holonomy sampling convergence, renormalized inner-product convergence, and a common vanishing-rate ledger are supplied for the Sprint113 residual decomposition, then the Sprint112 adjointness quadrature residual criterion is satisfied."

cellQuadratureSupplyText : String
cellQuadratureSupplyText =
  "Supply requirement: eps_cell(a,x_a,v) tends to zero on the Sprint112 admissible finite/continuum physical comparison window."

smoothingApproximationSupplyText : String
smoothingApproximationSupplyText =
  "Supply requirement: eps_smooth(a,x_a,v) tends to zero with the mollifier, patching, boundary-cell, and parallel-transport conventions used by the Sprint113 E_a candidate."

holonomySamplingSupplyText : String
holonomySamplingSupplyText =
  "Supply requirement: eps_hol(a,x_a,v) tends to zero for edge and plaquette holonomy sampling after finite physical projection and gauge quotienting."

renormalizedInnerProductSupplyText : String
renormalizedInnerProductSupplyText =
  "Supply requirement: eps_ren(a,x_a,v) tends to zero after fixing the shared Z(a), g(a), cell-volume, quotient-norm, and continuum Hilbert normalization conventions."

vanishingRateLedgerSupplyText : String
vanishingRateLedgerSupplyText =
  "Supply requirement: one ledger records a common a-window and rate comparison proving eps_cell + eps_smooth + eps_hol + eps_ren -> 0."

adjointnessClosureSatisfiedText : String
adjointnessClosureSatisfiedText =
  "Conclusion under supplies: residual_113(a,x_a,v) bounds the Sprint112 |<E_a x_a,v>_H_phys - <x_a,P_a v>_a,phys| residual and vanishes, so the adjointness residual closure criterion is satisfied."

approximateInverseSeparateText : String
approximateInverseSeparateText =
  "Separate lane: adjointness residual closure does not close E_a P_a or P_a E_a approximate inverse residuals unless explicit left and right inverse supplies are provided."

canonicalFailClosedBoundaryText : String
canonicalFailClosedBoundaryText =
  "Sprint114 records the conditional closure criterion.  The canonical receipt has no analytic supplies, no adjointness theorem proved here, no approximate inverse theorem proved here, no spectral passage, no mass gap, and no Clay Yang-Mills promotion."

cellQuadratureBlockerText : String
cellQuadratureBlockerText =
  "Exact blocker: no supplied cell quadrature convergence theorem is present in this canonical Sprint114 receipt."

smoothingApproximationBlockerText : String
smoothingApproximationBlockerText =
  "Exact blocker: no supplied smoothing approximation convergence theorem is present in this canonical Sprint114 receipt."

holonomySamplingBlockerText : String
holonomySamplingBlockerText =
  "Exact blocker: no supplied holonomy sampling convergence theorem is present in this canonical Sprint114 receipt."

renormalizedInnerProductBlockerText : String
renormalizedInnerProductBlockerText =
  "Exact blocker: no supplied renormalized inner-product convergence theorem is present in this canonical Sprint114 receipt."

vanishingRateLedgerBlockerText : String
vanishingRateLedgerBlockerText =
  "Exact blocker: no supplied common vanishing-rate ledger proves the combined Sprint113 residual tends to zero."

approximateInverseBlockerText : String
approximateInverseBlockerText =
  "Exact blocker: approximate inverse closure remains separate and no explicit left/right inverse residual supply is present."

nonPromotionBlockerText : String
nonPromotionBlockerText =
  "Exact blocker: Clay Yang-Mills promotion remains false because this module records a conditional residual closure criterion only."

data ClosureLane : Set where
  sprint113-estimate-lane :
    ClosureLane
  sprint112-reduction-lane :
    ClosureLane
  cell-quadrature-supply-lane :
    ClosureLane
  smoothing-approximation-supply-lane :
    ClosureLane
  holonomy-sampling-supply-lane :
    ClosureLane
  renormalized-inner-product-supply-lane :
    ClosureLane
  vanishing-rate-ledger-lane :
    ClosureLane
  adjointness-closure-criterion-lane :
    ClosureLane
  approximate-inverse-separate-lane :
    ClosureLane
  exact-blocker-lane :
    ClosureLane
  receipt-lane :
    ClosureLane

data ClosureStatus : Set where
  imported-sprint113-estimate :
    ClosureStatus
  imported-sprint112-reduction :
    ClosureStatus
  supply-required :
    ClosureStatus
  supply-recorded :
    ClosureStatus
  conditional-criterion-recorded :
    ClosureStatus
  adjointness-closure-satisfied-under-supplies :
    ClosureStatus
  approximate-inverse-explicit-supply-required :
    ClosureStatus
  exact-fail-closed-blocker :
    ClosureStatus
  fail-closed-nonpromotion :
    ClosureStatus

data SupplyKind : Set where
  cell-quadrature-convergence :
    SupplyKind
  smoothing-approximation-convergence :
    SupplyKind
  holonomy-sampling-convergence :
    SupplyKind
  renormalized-inner-product-convergence :
    SupplyKind
  combined-vanishing-rate-ledger :
    SupplyKind
  left-approximate-inverse-convergence :
    SupplyKind
  right-approximate-inverse-convergence :
    SupplyKind

data BlockerKind : Set where
  cell-quadrature-blocker :
    BlockerKind
  smoothing-approximation-blocker :
    BlockerKind
  holonomy-sampling-blocker :
    BlockerKind
  renormalized-inner-product-blocker :
    BlockerKind
  vanishing-rate-ledger-blocker :
    BlockerKind
  approximate-inverse-blocker :
    BlockerKind
  nonpromotion-blocker :
    BlockerKind

canonicalClosureLanes : List ClosureLane
canonicalClosureLanes =
  sprint113-estimate-lane
  ∷ sprint112-reduction-lane
  ∷ cell-quadrature-supply-lane
  ∷ smoothing-approximation-supply-lane
  ∷ holonomy-sampling-supply-lane
  ∷ renormalized-inner-product-supply-lane
  ∷ vanishing-rate-ledger-lane
  ∷ adjointness-closure-criterion-lane
  ∷ approximate-inverse-separate-lane
  ∷ exact-blocker-lane
  ∷ receipt-lane
  ∷ []

record ImportedResidualBase : Setω where
  constructor mkImportedResidualBase
  field
    sprint113Receipt :
      Estimate113.YMSprint113QuadratureResidualEstimateReceipt
    sprint112Receipt :
      Reduction112.YMSprint112AdjointnessApproxInverseReductionReceipt
    sprint113Path :
      String
    sprint112Path :
      String
    sprint113EstimateRecorded :
      Bool
    sprint112QuadratureCriterionRecorded :
      Bool
    sprint113TheoremProvedHere :
      Bool
    sprint113TheoremProvedHereIsFalse :
      sprint113TheoremProvedHere ≡ false
    sprint112ReductionProvedHere :
      Bool
    sprint112ReductionProvedHereIsFalse :
      sprint112ReductionProvedHere ≡ false

record ConvergenceSupply : Set where
  constructor mkConvergenceSupply
  field
    kind :
      SupplyKind
    lane :
      ClosureLane
    statement :
      String
    residualSymbol :
      String
    admissibleWindow :
      String
    rateSymbol :
      String
    supplied :
      Bool
    status :
      ClosureStatus

record VanishingRateLedger : Set where
  constructor mkVanishingRateLedger
  field
    lane :
      ClosureLane
    statement :
      String
    commonWindow :
      String
    cellRate :
      String
    smoothingRate :
      String
    holonomyRate :
      String
    renormalizationRate :
      String
    combinedRate :
      String
    allRatesSupplied :
      Bool
    combinedResidualVanishes :
      Bool
    status :
      ClosureStatus

record SuppliedAdjointnessResidualPackage : Setω where
  constructor mkSuppliedAdjointnessResidualPackage
  field
    importedBase :
      ImportedResidualBase
    cellQuadratureSupply :
      ConvergenceSupply
    smoothingApproximationSupply :
      ConvergenceSupply
    holonomySamplingSupply :
      ConvergenceSupply
    renormalizedInnerProductSupply :
      ConvergenceSupply
    vanishingRateLedger :
      VanishingRateLedger
    cellQuadratureSupplied :
      Bool
    smoothingApproximationSupplied :
      Bool
    holonomySamplingSupplied :
      Bool
    renormalizedInnerProductSupplied :
      Bool
    vanishingRateLedgerSupplied :
      Bool
    allAdjointnessSuppliesPresent :
      Bool

record AdjointnessResidualClosureCriterion : Setω where
  constructor mkAdjointnessResidualClosureCriterion
  field
    lane :
      ClosureLane
    statement :
      String
    suppliedPackage :
      SuppliedAdjointnessResidualPackage
    sprint112Criterion :
      Reduction112.QuadratureResidualCriterion
    sprint113Target :
      Estimate113.AdjointnessResidualTarget
    residualBound :
      String
    closureSatisfied :
      Bool
    closureStatus :
      ClosureStatus
    approximateInverseClosedByThisCriterion :
      Bool
    approximateInverseClosedByThisCriterionIsFalse :
      approximateInverseClosedByThisCriterion ≡ false

record ApproximateInverseSupply : Set where
  constructor mkApproximateInverseSupply
  field
    leftInverseSupply :
      ConvergenceSupply
    rightInverseSupply :
      ConvergenceSupply
    leftInverseSupplied :
      Bool
    rightInverseSupplied :
      Bool
    bothInverseSuppliesPresent :
      Bool

record ApproximateInverseClosureCriterion : Setω where
  constructor mkApproximateInverseClosureCriterion
  field
    lane :
      ClosureLane
    statement :
      String
    suppliedAdjointnessCriterion :
      AdjointnessResidualClosureCriterion
    approximateInverseSupply :
      ApproximateInverseSupply
    sprint112LeftResidual :
      Reduction112.ApproximateInverseResidual
    sprint112RightResidual :
      Reduction112.ApproximateInverseResidual
    closureSatisfied :
      Bool
    status :
      ClosureStatus

record ExactBlocker : Set where
  constructor mkExactBlocker
  field
    kind :
      BlockerKind
    lane :
      ClosureLane
    statement :
      String
    sourcePath :
      String
    blocksCanonicalClosure :
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
    blockers :
      List ExactBlocker
    blockerTexts :
      List String
    exactBlockersRecorded :
      Bool
    canonicalSuppliesAvailable :
      Bool
    canonicalSuppliesAvailableIsFalse :
      canonicalSuppliesAvailable ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ClosureStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      ClosureLane
    statement :
      String
    conditionalCriterionRecorded :
      Bool
    canonicalSuppliesAvailableHereFlag :
      Bool
    canonicalSuppliesAvailableHereIsFalse :
      canonicalSuppliesAvailableHereFlag ≡ false
    adjointnessResidualClosureProvedHereFlag :
      Bool
    adjointnessResidualClosureProvedHereIsFalse :
      adjointnessResidualClosureProvedHereFlag ≡ false
    approximateInverseClosureProvedHereFlag :
      Bool
    approximateInverseClosureProvedHereIsFalse :
      approximateInverseClosureProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ClosureStatus

record YMSprint114QuadratureResidualClosureCriterionReceipt : Setω where
  constructor mkYMSprint114QuadratureResidualClosureCriterionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedBase :
      ImportedResidualBase
    closureCriterionTextRecorded :
      String
    canonicalBlockers :
      ExactBlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ClosureLane
    evidenceLedger :
      List String
    approximateInverseKeptSeparateHere :
      Bool
    receiptRecorded :
      Bool
    canonicalSuppliesAvailableHereReceipt :
      Bool
    canonicalSuppliesAvailableHereReceiptIsFalse :
      canonicalSuppliesAvailableHereReceipt ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open ImportedResidualBase public
open ConvergenceSupply public
open VanishingRateLedger public
open SuppliedAdjointnessResidualPackage public
open AdjointnessResidualClosureCriterion public
open ApproximateInverseSupply public
open ApproximateInverseClosureCriterion public
open ExactBlocker public
open ExactBlockerLedger public
open TheoremBoundary public
open YMSprint114QuadratureResidualClosureCriterionReceipt public

canonicalImportedResidualBase : ImportedResidualBase
canonicalImportedResidualBase =
  mkImportedResidualBase
    Estimate113.canonicalReceipt
    Reduction112.canonicalReceipt
    estimate113Path
    reduction112Path
    Estimate113.quadratureResidualEstimateRecorded
    Reduction112.quadratureResidualCriterionRecorded
    Estimate113.quadratureResidualTheoremProvedHere
    refl
    Reduction112.adjointnessReducedAndProvedHere
    refl

buildAdjointnessResidualClosureCriterion :
  SuppliedAdjointnessResidualPackage ->
  AdjointnessResidualClosureCriterion
buildAdjointnessResidualClosureCriterion supplied =
  mkAdjointnessResidualClosureCriterion
    adjointness-closure-criterion-lane
    adjointnessClosureSatisfiedText
    supplied
    (Reduction112.quadratureResidual
      (ImportedResidualBase.sprint112Receipt
        (SuppliedAdjointnessResidualPackage.importedBase supplied)))
    (Estimate113.adjointnessResidualTarget
      (ImportedResidualBase.sprint113Receipt
        (SuppliedAdjointnessResidualPackage.importedBase supplied)))
    "|<E_a x_a,v>_H_phys - <x_a,P_a v>_a,phys| <= eps_cell + eps_smooth + eps_hol + eps_ren -> 0"
    (SuppliedAdjointnessResidualPackage.allAdjointnessSuppliesPresent supplied)
    adjointness-closure-satisfied-under-supplies
    false
    refl

buildApproximateInverseClosureCriterion :
  AdjointnessResidualClosureCriterion ->
  ApproximateInverseSupply ->
  ApproximateInverseClosureCriterion
buildApproximateInverseClosureCriterion adjointnessCriterion inverseSupply =
  mkApproximateInverseClosureCriterion
    approximate-inverse-separate-lane
    approximateInverseSeparateText
    adjointnessCriterion
    inverseSupply
    (Reduction112.leftInverseResidual
      (ImportedResidualBase.sprint112Receipt
        (SuppliedAdjointnessResidualPackage.importedBase
          (AdjointnessResidualClosureCriterion.suppliedPackage
            adjointnessCriterion))))
    (Reduction112.rightInverseResidual
      (ImportedResidualBase.sprint112Receipt
        (SuppliedAdjointnessResidualPackage.importedBase
          (AdjointnessResidualClosureCriterion.suppliedPackage
            adjointnessCriterion))))
    (ApproximateInverseSupply.bothInverseSuppliesPresent inverseSupply)
    approximate-inverse-explicit-supply-required

canonicalCellQuadratureSupplyRequired : ConvergenceSupply
canonicalCellQuadratureSupplyRequired =
  mkConvergenceSupply
    cell-quadrature-convergence
    cell-quadrature-supply-lane
    cellQuadratureSupplyText
    "eps_cell(a,x_a,v)"
    "0 < a <= a0"
    "rho_cell(a)"
    false
    supply-required

canonicalSmoothingApproximationSupplyRequired : ConvergenceSupply
canonicalSmoothingApproximationSupplyRequired =
  mkConvergenceSupply
    smoothing-approximation-convergence
    smoothing-approximation-supply-lane
    smoothingApproximationSupplyText
    "eps_smooth(a,x_a,v)"
    "rho(a) comparable to a in the Sprint113 smoothing convention"
    "rho_smooth(a)"
    false
    supply-required

canonicalHolonomySamplingSupplyRequired : ConvergenceSupply
canonicalHolonomySamplingSupplyRequired =
  mkConvergenceSupply
    holonomy-sampling-convergence
    holonomy-sampling-supply-lane
    holonomySamplingSupplyText
    "eps_hol(a,x_a,v)"
    "edge and plaquette sampling window"
    "rho_hol(a)"
    false
    supply-required

canonicalRenormalizedInnerProductSupplyRequired : ConvergenceSupply
canonicalRenormalizedInnerProductSupplyRequired =
  mkConvergenceSupply
    renormalized-inner-product-convergence
    renormalized-inner-product-supply-lane
    renormalizedInnerProductSupplyText
    "eps_ren(a,x_a,v)"
    "shared Z(a), g(a), volume, quotient, and Hilbert normalization window"
    "rho_ren(a)"
    false
    supply-required

canonicalVanishingRateLedgerRequired : VanishingRateLedger
canonicalVanishingRateLedgerRequired =
  mkVanishingRateLedger
    vanishing-rate-ledger-lane
    vanishingRateLedgerSupplyText
    "0 < a <= a0 with one normalization convention"
    "rho_cell(a)"
    "rho_smooth(a)"
    "rho_hol(a)"
    "rho_ren(a)"
    "rho_total(a) = rho_cell(a) + rho_smooth(a) + rho_hol(a) + rho_ren(a)"
    false
    false
    supply-required

canonicalSuppliedAdjointnessResidualPackage :
  SuppliedAdjointnessResidualPackage
canonicalSuppliedAdjointnessResidualPackage =
  mkSuppliedAdjointnessResidualPackage
    canonicalImportedResidualBase
    canonicalCellQuadratureSupplyRequired
    canonicalSmoothingApproximationSupplyRequired
    canonicalHolonomySamplingSupplyRequired
    canonicalRenormalizedInnerProductSupplyRequired
    canonicalVanishingRateLedgerRequired
    false
    false
    false
    false
    false
    false

canonicalConditionalAdjointnessCriterion :
  AdjointnessResidualClosureCriterion
canonicalConditionalAdjointnessCriterion =
  buildAdjointnessResidualClosureCriterion
    canonicalSuppliedAdjointnessResidualPackage

canonicalLeftInverseSupplyRequired : ConvergenceSupply
canonicalLeftInverseSupplyRequired =
  mkConvergenceSupply
    left-approximate-inverse-convergence
    approximate-inverse-separate-lane
    Reduction112.leftInverseResidualText
    "eps_left(a,v)"
    "continuum finite-energy physical comparison sector"
    "rho_left(a)"
    false
    approximate-inverse-explicit-supply-required

canonicalRightInverseSupplyRequired : ConvergenceSupply
canonicalRightInverseSupplyRequired =
  mkConvergenceSupply
    right-approximate-inverse-convergence
    approximate-inverse-separate-lane
    Reduction112.rightInverseResidualText
    "eps_right(a,u)"
    "finite physical gauge-quotient comparison sector"
    "rho_right(a)"
    false
    approximate-inverse-explicit-supply-required

canonicalApproximateInverseSupply : ApproximateInverseSupply
canonicalApproximateInverseSupply =
  mkApproximateInverseSupply
    canonicalLeftInverseSupplyRequired
    canonicalRightInverseSupplyRequired
    false
    false
    false

canonicalApproximateInverseClosureCriterion :
  ApproximateInverseClosureCriterion
canonicalApproximateInverseClosureCriterion =
  buildApproximateInverseClosureCriterion
    canonicalConditionalAdjointnessCriterion
    canonicalApproximateInverseSupply

canonicalCellQuadratureBlocker : ExactBlocker
canonicalCellQuadratureBlocker =
  mkExactBlocker
    cell-quadrature-blocker
    exact-blocker-lane
    cellQuadratureBlockerText
    estimate113Path
    true
    cellQuadratureConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalSmoothingApproximationBlocker : ExactBlocker
canonicalSmoothingApproximationBlocker =
  mkExactBlocker
    smoothing-approximation-blocker
    exact-blocker-lane
    smoothingApproximationBlockerText
    estimate113Path
    true
    smoothingApproximationConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalHolonomySamplingBlocker : ExactBlocker
canonicalHolonomySamplingBlocker =
  mkExactBlocker
    holonomy-sampling-blocker
    exact-blocker-lane
    holonomySamplingBlockerText
    estimate113Path
    true
    holonomySamplingConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalRenormalizedInnerProductBlocker : ExactBlocker
canonicalRenormalizedInnerProductBlocker =
  mkExactBlocker
    renormalized-inner-product-blocker
    exact-blocker-lane
    renormalizedInnerProductBlockerText
    estimate113Path
    true
    renormalizedInnerProductConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalVanishingRateLedgerBlocker : ExactBlocker
canonicalVanishingRateLedgerBlocker =
  mkExactBlocker
    vanishing-rate-ledger-blocker
    exact-blocker-lane
    vanishingRateLedgerBlockerText
    modulePath
    true
    vanishingRateLedgerProvedHere
    refl
    exact-fail-closed-blocker

canonicalApproximateInverseBlocker : ExactBlocker
canonicalApproximateInverseBlocker =
  mkExactBlocker
    approximate-inverse-blocker
    approximate-inverse-separate-lane
    approximateInverseBlockerText
    reduction112Path
    true
    approximateInverseClosureProvedHere
    refl
    approximate-inverse-explicit-supply-required

canonicalNonPromotionBlocker : ExactBlocker
canonicalNonPromotionBlocker =
  mkExactBlocker
    nonpromotion-blocker
    receipt-lane
    nonPromotionBlockerText
    modulePath
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalExactBlockers : List ExactBlocker
canonicalExactBlockers =
  canonicalCellQuadratureBlocker
  ∷ canonicalSmoothingApproximationBlocker
  ∷ canonicalHolonomySamplingBlocker
  ∷ canonicalRenormalizedInnerProductBlocker
  ∷ canonicalVanishingRateLedgerBlocker
  ∷ canonicalApproximateInverseBlocker
  ∷ canonicalNonPromotionBlocker
  ∷ []

canonicalExactBlockerLedger : ExactBlockerLedger
canonicalExactBlockerLedger =
  mkExactBlockerLedger
    exact-blocker-lane
    canonicalExactBlockers
    (cellQuadratureBlockerText
     ∷ smoothingApproximationBlockerText
     ∷ holonomySamplingBlockerText
     ∷ renormalizedInnerProductBlockerText
     ∷ vanishingRateLedgerBlockerText
     ∷ approximateInverseBlockerText
     ∷ nonPromotionBlockerText
     ∷ [])
    true
    canonicalSuppliesAvailableHere
    refl
    clayYangMillsPromoted
    refl
    exact-fail-closed-blocker

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    receipt-lane
    canonicalFailClosedBoundaryText
    quadratureResidualClosureCriterionRecorded
    canonicalSuppliesAvailableHere
    refl
    adjointnessResidualClosureProvedHere
    refl
    approximateInverseClosureProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint114QuadratureResidualClosureCriterionReceipt :
  YMSprint114QuadratureResidualClosureCriterionReceipt
canonicalYMSprint114QuadratureResidualClosureCriterionReceipt =
  mkYMSprint114QuadratureResidualClosureCriterionReceipt
    sprintNumber
    modulePath
    canonicalImportedResidualBase
    closureCriterionText
    canonicalExactBlockerLedger
    canonicalTheoremBoundary
    canonicalClosureLanes
    (closureCriterionText
     ∷ cellQuadratureSupplyText
     ∷ smoothingApproximationSupplyText
     ∷ holonomySamplingSupplyText
     ∷ renormalizedInnerProductSupplyText
     ∷ vanishingRateLedgerSupplyText
     ∷ adjointnessClosureSatisfiedText
     ∷ approximateInverseSeparateText
     ∷ canonicalFailClosedBoundaryText
     ∷ cellQuadratureBlockerText
     ∷ smoothingApproximationBlockerText
     ∷ holonomySamplingBlockerText
     ∷ renormalizedInnerProductBlockerText
     ∷ vanishingRateLedgerBlockerText
     ∷ approximateInverseBlockerText
     ∷ nonPromotionBlockerText
     ∷ [])
    approximateInverseKeptSeparate
    quadratureResidualClosureCriterionRecorded
    canonicalSuppliesAvailableHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint114QuadratureResidualClosureCriterionReceipt
canonicalReceipt =
  canonicalYMSprint114QuadratureResidualClosureCriterionReceipt

canonicalCriterionApproximateInverseClosedByThisIsFalse :
  approximateInverseClosedByThisCriterion
    canonicalConditionalAdjointnessCriterion ≡ false
canonicalCriterionApproximateInverseClosedByThisIsFalse =
  refl

canonicalReceiptSuppliesAvailableHereIsFalse :
  canonicalSuppliesAvailableHereReceipt canonicalReceipt ≡ false
canonicalReceiptSuppliesAvailableHereIsFalse =
  refl

canonicalAdjointnessResidualClosureProvedHereIsFalse :
  TheoremBoundary.adjointnessResidualClosureProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalAdjointnessResidualClosureProvedHereIsFalse =
  refl

canonicalApproximateInverseClosureProvedHereIsFalse :
  TheoremBoundary.approximateInverseClosureProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalApproximateInverseClosureProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptBlockers : List ExactBlocker
canonicalReceiptBlockers =
  blockers (canonicalBlockers canonicalReceipt)

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
