module DASHI.Physics.Closure.YMSprint113QuadratureResidualEstimate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112AdjointnessApproxInverseReduction
  as Reduction112
import DASHI.Physics.Closure.YMSprint112ContinuumSamplingProjectionMapCandidate
  as Sampling112
import DASHI.Physics.Closure.YMSprint112RenormalizedInterpolationMapCandidate
  as Interpolation112

------------------------------------------------------------------------
-- Sprint 113 quadrature residual estimate ledger.
--
-- This module records the residual estimates needed after Sprint112:
-- cell quadrature, smoothing approximation, holonomy sampling error,
-- renormalized inner-product comparison, and the adjointness residual
-- target.  It is intentionally fail-closed: the estimates are structured
-- and inhabited, but no analytic convergence theorem, approximate inverse
-- theorem, adjointness theorem, or Clay Yang-Mills promotion is proved here.

sprintNumber : Nat
sprintNumber = 113

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint113QuadratureResidualEstimate.agda"

reduction112Path : String
reduction112Path =
  "DASHI/Physics/Closure/YMSprint112AdjointnessApproxInverseReduction.agda"

sampling112Path : String
sampling112Path =
  "DASHI/Physics/Closure/YMSprint112ContinuumSamplingProjectionMapCandidate.agda"

interpolation112Path : String
interpolation112Path =
  "DASHI/Physics/Closure/YMSprint112RenormalizedInterpolationMapCandidate.agda"

quadratureResidualEstimateRecorded : Bool
quadratureResidualEstimateRecorded = true

cellQuadratureEstimateRecorded : Bool
cellQuadratureEstimateRecorded = true

smoothingApproximationEstimateRecorded : Bool
smoothingApproximationEstimateRecorded = true

holonomySamplingErrorEstimateRecorded : Bool
holonomySamplingErrorEstimateRecorded = true

renormalizedInnerProductComparisonRecorded : Bool
renormalizedInnerProductComparisonRecorded = true

adjointnessResidualTargetRecorded : Bool
adjointnessResidualTargetRecorded = true

failClosedBlockersRecorded : Bool
failClosedBlockersRecorded = true

cellQuadratureConvergenceProvedHere : Bool
cellQuadratureConvergenceProvedHere = false

smoothingApproximationConvergenceProvedHere : Bool
smoothingApproximationConvergenceProvedHere = false

holonomySamplingConvergenceProvedHere : Bool
holonomySamplingConvergenceProvedHere = false

renormalizedInnerProductConvergenceProvedHere : Bool
renormalizedInnerProductConvergenceProvedHere = false

adjointnessResidualVanishesProvedHere : Bool
adjointnessResidualVanishesProvedHere = false

approximateInverseResidualVanishesProvedHere : Bool
approximateInverseResidualVanishesProvedHere = false

quadratureResidualTheoremProvedHere : Bool
quadratureResidualTheoremProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

cellQuadratureEstimateText : String
cellQuadratureEstimateText =
  "Cell quadrature estimate: decompose <E_a x_a , v>_H_phys into a finite sum over lattice cells, compare each renormalized cell integral with the finite physical inner-product summand, and record a residual eps_cell(a,x_a,v) for the admissible Sprint112 window."

smoothingApproximationEstimateText : String
smoothingApproximationEstimateText =
  "Smoothing approximation estimate: compare the mollified parallel-transported local section used by E_a with the unsmoothed cell field, recording eps_smooth(a,x_a,v) for mollifier scale comparable to a."

holonomySamplingErrorEstimateText : String
holonomySamplingErrorEstimateText =
  "Holonomy sampling error estimate: compare P_a v obtained from edge and plaquette holonomy samples with the continuum local field data paired against x_a, recording eps_hol(a,x_a,v) after finite physical projection and gauge quotienting."

renormalizedInnerProductComparisonText : String
renormalizedInnerProductComparisonText =
  "Renormalized inner-product comparison: align the Sprint112 Z(a), g(a), cell-volume, quotient-norm, and physical projection conventions so |<E_a x_a , v>_H_phys - <x_a , P_a v>_a,phys| is bounded by eps_cell + eps_smooth + eps_hol + eps_ren."

adjointnessResidualTargetText : String
adjointnessResidualTargetText =
  "Adjointness residual target: prove a uniform bound residual_113(a,x_a,v) -> 0 for finite physical x_a and continuum finite-energy physical v, thereby feeding the Sprint112 adjointness residual criterion without claiming it here."

exactCellQuadratureBlockerText : String
exactCellQuadratureBlockerText =
  "Exact fail-closed blocker: no DASHI-native theorem proves the cell quadrature residual eps_cell(a,x_a,v) tends to zero uniformly on the Sprint112 admissible comparison window."

exactSmoothingBlockerText : String
exactSmoothingBlockerText =
  "Exact fail-closed blocker: no proof controls mollification, patching, boundary cells, and parallel-transport smoothing error for the recorded E_a candidate."

exactHolonomySamplingBlockerText : String
exactHolonomySamplingBlockerText =
  "Exact fail-closed blocker: no proof controls path-ordered edge and plaquette holonomy sampling error for the recorded P_a candidate after finite physical projection and quotienting."

exactRenormalizedInnerProductBlockerText : String
exactRenormalizedInnerProductBlockerText =
  "Exact fail-closed blocker: no proof identifies the finite and continuum renormalized inner products under a common Z(a), g(a), cell-volume, and quotient normalization convention."

exactAdjointnessResidualBlockerText : String
exactAdjointnessResidualBlockerText =
  "Exact fail-closed blocker: no proof shows the combined Sprint113 residual bound vanishes, so the Sprint112 adjointness reduction remains open."

exactApproximateInverseBlockerText : String
exactApproximateInverseBlockerText =
  "Exact fail-closed blocker: no proof converts the quadrature residual comparison into left or right approximate inverse convergence for E_a P_a or P_a E_a."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint113 records quadrature residual estimate obligations only; it does not prove adjointness, approximate inverse laws, Mosco convergence, spectral passage, mass gap, or Clay Yang-Mills."

data ResidualLane : Set where
  sprint112-import-lane :
    ResidualLane
  cell-quadrature-lane :
    ResidualLane
  smoothing-approximation-lane :
    ResidualLane
  holonomy-sampling-error-lane :
    ResidualLane
  renormalized-inner-product-lane :
    ResidualLane
  adjointness-residual-target-lane :
    ResidualLane
  exact-fail-closed-blocker-lane :
    ResidualLane
  receipt-lane :
    ResidualLane

data ResidualStatus : Set where
  imported-sprint112-support :
    ResidualStatus
  estimate-recorded :
    ResidualStatus
  residual-target-recorded :
    ResidualStatus
  analytic-proof-required :
    ResidualStatus
  exact-fail-closed-blocker :
    ResidualStatus
  theorem-open :
    ResidualStatus
  fail-closed-nonpromotion :
    ResidualStatus

data ResidualComponent : Set where
  eps-cell :
    ResidualComponent
  eps-smooth :
    ResidualComponent
  eps-holonomy :
    ResidualComponent
  eps-renormalization :
    ResidualComponent
  eps-total-adjointness :
    ResidualComponent

data BlockerKind : Set where
  cell-quadrature-blocker :
    BlockerKind
  smoothing-approximation-blocker :
    BlockerKind
  holonomy-sampling-blocker :
    BlockerKind
  renormalized-inner-product-blocker :
    BlockerKind
  adjointness-residual-blocker :
    BlockerKind
  approximate-inverse-blocker :
    BlockerKind
  nonpromotion-blocker :
    BlockerKind

canonicalResidualLanes : List ResidualLane
canonicalResidualLanes =
  sprint112-import-lane
  ∷ cell-quadrature-lane
  ∷ smoothing-approximation-lane
  ∷ holonomy-sampling-error-lane
  ∷ renormalized-inner-product-lane
  ∷ adjointness-residual-target-lane
  ∷ exact-fail-closed-blocker-lane
  ∷ receipt-lane
  ∷ []

canonicalResidualComponents : List ResidualComponent
canonicalResidualComponents =
  eps-cell
  ∷ eps-smooth
  ∷ eps-holonomy
  ∷ eps-renormalization
  ∷ eps-total-adjointness
  ∷ []

record Sprint112Inputs : Setω where
  constructor mkSprint112Inputs
  field
    reductionReceipt :
      Reduction112.YMSprint112AdjointnessApproxInverseReductionReceipt
    samplingReceipt :
      Sampling112.SamplingProjectionCandidateReceipt
    interpolationReceipt :
      Interpolation112.YMSprint112RenormalizedInterpolationMapCandidateReceipt
    reductionSourcePath :
      String
    samplingSourcePath :
      String
    interpolationSourcePath :
      String
    reductionRecorded :
      Bool
    samplingCandidateRecorded :
      Bool
    interpolationCandidateRecorded :
      Bool
    importedQuadratureResidualProved :
      Bool
    importedSamplingMapConstructed :
      Bool
    importedInterpolationMapConstructed :
      Bool
    importedQuadratureResidualProvedIsFalse :
      importedQuadratureResidualProved ≡ false
    importedSamplingMapConstructedIsFalse :
      importedSamplingMapConstructed ≡ false
    importedInterpolationMapConstructedIsFalse :
      importedInterpolationMapConstructed ≡ false

record ResidualEstimate : Set where
  constructor mkResidualEstimate
  field
    lane :
      ResidualLane
    component :
      ResidualComponent
    statement :
      String
    residualSymbol :
      String
    finiteInputSymbol :
      String
    continuumInputSymbol :
      String
    comparisonWindow :
      String
    sourceMap :
      String
    estimateRecorded :
      Bool
    convergenceProvedHere :
      Bool
    convergenceProvedHereIsFalse :
      convergenceProvedHere ≡ false
    status :
      ResidualStatus

record RenormalizedInnerProductComparison : Set where
  constructor mkRenormalizedInnerProductComparison
  field
    lane :
      ResidualLane
    statement :
      String
    continuumInnerProductSymbol :
      String
    finiteInnerProductSymbol :
      String
    embeddingSymbol :
      String
    projectionSymbol :
      String
    renormalizationTerms :
      List String
    residualComponents :
      List ResidualComponent
    comparisonRecorded :
      Bool
    convergenceProvedHere :
      Bool
    convergenceProvedHereIsFalse :
      convergenceProvedHere ≡ false
    status :
      ResidualStatus

record AdjointnessResidualTarget : Set where
  constructor mkAdjointnessResidualTarget
  field
    lane :
      ResidualLane
    statement :
      String
    targetResidualSymbol :
      String
    targetBoundText :
      String
    feedsSprint112Reduction :
      Bool
    targetRecorded :
      Bool
    residualVanishesProvedHere :
      Bool
    residualVanishesProvedHereIsFalse :
      residualVanishesProvedHere ≡ false
    approximateInverseFedHere :
      Bool
    approximateInverseFedHereIsFalse :
      approximateInverseFedHere ≡ false
    status :
      ResidualStatus

record ExactFailClosedBlocker : Set where
  constructor mkExactFailClosedBlocker
  field
    kind :
      BlockerKind
    lane :
      ResidualLane
    statement :
      String
    sourcePath :
      String
    blocksPromotion :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ResidualStatus

record BlockerLedger : Set where
  constructor mkBlockerLedger
  field
    lane :
      ResidualLane
    cellQuadratureBlocker :
      String
    smoothingApproximationBlocker :
      String
    holonomySamplingBlocker :
      String
    renormalizedInnerProductBlocker :
      String
    adjointnessResidualBlocker :
      String
    approximateInverseBlocker :
      String
    nonPromotionBlocker :
      String
    exactBlockers :
      List ExactFailClosedBlocker
    blockerTexts :
      List String
    ledgerRecorded :
      Bool
    status :
      ResidualStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      ResidualLane
    statement :
      String
    cellQuadratureConvergenceProvedHereFlag :
      Bool
    cellQuadratureConvergenceProvedHereIsFalse :
      cellQuadratureConvergenceProvedHereFlag ≡ false
    smoothingApproximationConvergenceProvedHereFlag :
      Bool
    smoothingApproximationConvergenceProvedHereIsFalse :
      smoothingApproximationConvergenceProvedHereFlag ≡ false
    holonomySamplingConvergenceProvedHereFlag :
      Bool
    holonomySamplingConvergenceProvedHereIsFalse :
      holonomySamplingConvergenceProvedHereFlag ≡ false
    renormalizedInnerProductConvergenceProvedHereFlag :
      Bool
    renormalizedInnerProductConvergenceProvedHereIsFalse :
      renormalizedInnerProductConvergenceProvedHereFlag ≡ false
    adjointnessResidualVanishesProvedHereFlag :
      Bool
    adjointnessResidualVanishesProvedHereIsFalse :
      adjointnessResidualVanishesProvedHereFlag ≡ false
    quadratureResidualTheoremProvedHereFlag :
      Bool
    quadratureResidualTheoremProvedHereIsFalse :
      quadratureResidualTheoremProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ResidualStatus

record YMSprint113QuadratureResidualEstimateReceipt : Setω where
  constructor mkYMSprint113QuadratureResidualEstimateReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sprint112Inputs :
      Sprint112Inputs
    cellQuadratureEstimate :
      ResidualEstimate
    smoothingApproximationEstimate :
      ResidualEstimate
    holonomySamplingErrorEstimate :
      ResidualEstimate
    renormalizedInnerProductComparison :
      RenormalizedInnerProductComparison
    adjointnessResidualTarget :
      AdjointnessResidualTarget
    blockers :
      BlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ResidualLane
    components :
      List ResidualComponent
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    failClosedBlockersRecordedHere :
      Bool
    quadratureResidualTheoremProvedHereReceipt :
      Bool
    quadratureResidualTheoremProvedHereReceiptIsFalse :
      quadratureResidualTheoremProvedHereReceipt ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open Sprint112Inputs public
open ResidualEstimate public
open RenormalizedInnerProductComparison public
open AdjointnessResidualTarget public
open ExactFailClosedBlocker public
open BlockerLedger public
open TheoremBoundary public
open YMSprint113QuadratureResidualEstimateReceipt public

canonicalSprint112Inputs : Sprint112Inputs
canonicalSprint112Inputs =
  mkSprint112Inputs
    Reduction112.canonicalReceipt
    Sampling112.canonicalReceipt
    Interpolation112.canonicalReceipt
    reduction112Path
    sampling112Path
    interpolation112Path
    Reduction112.adjointnessReductionRecorded
    Sampling112.samplingProjectionCandidateRecorded
    Interpolation112.interpolationCandidateRecorded
    Reduction112.quadratureResidualEstimateProvedHere
    Sampling112.samplingProjectionMapConstructedHere
    Interpolation112.interpolationMapConstructedHere
    refl
    refl
    refl

canonicalCellQuadratureEstimate : ResidualEstimate
canonicalCellQuadratureEstimate =
  mkResidualEstimate
    cell-quadrature-lane
    eps-cell
    cellQuadratureEstimateText
    "eps_cell(a,x_a,v)"
    "x_a : H_a,phys / gauge"
    "v : H_phys finite-energy"
    "0 < a <= a0"
    "E_a cell interpolation"
    cellQuadratureEstimateRecorded
    cellQuadratureConvergenceProvedHere
    refl
    estimate-recorded

canonicalSmoothingApproximationEstimate : ResidualEstimate
canonicalSmoothingApproximationEstimate =
  mkResidualEstimate
    smoothing-approximation-lane
    eps-smooth
    smoothingApproximationEstimateText
    "eps_smooth(a,x_a,v)"
    "x_a : H_a,phys / gauge"
    "v : H_phys finite-energy"
    "mollifier scale rho(a) comparable to a"
    "E_a smoothing candidate"
    smoothingApproximationEstimateRecorded
    smoothingApproximationConvergenceProvedHere
    refl
    estimate-recorded

canonicalHolonomySamplingErrorEstimate : ResidualEstimate
canonicalHolonomySamplingErrorEstimate =
  mkResidualEstimate
    holonomy-sampling-error-lane
    eps-holonomy
    holonomySamplingErrorEstimateText
    "eps_hol(a,x_a,v)"
    "x_a : H_a,phys / gauge"
    "v : H_phys finite-energy"
    "plaquette and edge sampling window"
    "P_a holonomy sampling candidate"
    holonomySamplingErrorEstimateRecorded
    holonomySamplingConvergenceProvedHere
    refl
    estimate-recorded

canonicalRenormalizedInnerProductComparison :
  RenormalizedInnerProductComparison
canonicalRenormalizedInnerProductComparison =
  mkRenormalizedInnerProductComparison
    renormalized-inner-product-lane
    renormalizedInnerProductComparisonText
    "<E_a x_a , v>_H_phys"
    "<x_a , P_a v>_a,phys"
    "E_a"
    "P_a"
    ("Z(a)"
     ∷ "g(a)"
     ∷ "cell-volume normalization"
     ∷ "finite physical quotient norm"
     ∷ "continuum physical Hilbert norm"
     ∷ [])
    canonicalResidualComponents
    renormalizedInnerProductComparisonRecorded
    renormalizedInnerProductConvergenceProvedHere
    refl
    residual-target-recorded

canonicalAdjointnessResidualTarget : AdjointnessResidualTarget
canonicalAdjointnessResidualTarget =
  mkAdjointnessResidualTarget
    adjointness-residual-target-lane
    adjointnessResidualTargetText
    "residual_113(a,x_a,v)"
    "|<E_a x_a , v>_H_phys - <x_a , P_a v>_a,phys| <= eps_cell + eps_smooth + eps_hol + eps_ren"
    true
    adjointnessResidualTargetRecorded
    adjointnessResidualVanishesProvedHere
    refl
    approximateInverseResidualVanishesProvedHere
    refl
    theorem-open

canonicalCellQuadratureBlockerReceipt : ExactFailClosedBlocker
canonicalCellQuadratureBlockerReceipt =
  mkExactFailClosedBlocker
    cell-quadrature-blocker
    exact-fail-closed-blocker-lane
    exactCellQuadratureBlockerText
    reduction112Path
    true
    cellQuadratureConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalSmoothingApproximationBlockerReceipt : ExactFailClosedBlocker
canonicalSmoothingApproximationBlockerReceipt =
  mkExactFailClosedBlocker
    smoothing-approximation-blocker
    exact-fail-closed-blocker-lane
    exactSmoothingBlockerText
    interpolation112Path
    true
    smoothingApproximationConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalHolonomySamplingBlockerReceipt : ExactFailClosedBlocker
canonicalHolonomySamplingBlockerReceipt =
  mkExactFailClosedBlocker
    holonomy-sampling-blocker
    exact-fail-closed-blocker-lane
    exactHolonomySamplingBlockerText
    sampling112Path
    true
    holonomySamplingConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalRenormalizedInnerProductBlockerReceipt : ExactFailClosedBlocker
canonicalRenormalizedInnerProductBlockerReceipt =
  mkExactFailClosedBlocker
    renormalized-inner-product-blocker
    exact-fail-closed-blocker-lane
    exactRenormalizedInnerProductBlockerText
    reduction112Path
    true
    renormalizedInnerProductConvergenceProvedHere
    refl
    exact-fail-closed-blocker

canonicalAdjointnessResidualBlockerReceipt : ExactFailClosedBlocker
canonicalAdjointnessResidualBlockerReceipt =
  mkExactFailClosedBlocker
    adjointness-residual-blocker
    exact-fail-closed-blocker-lane
    exactAdjointnessResidualBlockerText
    reduction112Path
    true
    adjointnessResidualVanishesProvedHere
    refl
    exact-fail-closed-blocker

canonicalApproximateInverseBlockerReceipt : ExactFailClosedBlocker
canonicalApproximateInverseBlockerReceipt =
  mkExactFailClosedBlocker
    approximate-inverse-blocker
    exact-fail-closed-blocker-lane
    exactApproximateInverseBlockerText
    reduction112Path
    true
    approximateInverseResidualVanishesProvedHere
    refl
    exact-fail-closed-blocker

canonicalNonPromotionBlockerReceipt : ExactFailClosedBlocker
canonicalNonPromotionBlockerReceipt =
  mkExactFailClosedBlocker
    nonpromotion-blocker
    exact-fail-closed-blocker-lane
    nonPromotionBoundaryText
    modulePath
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalExactBlockers : List ExactFailClosedBlocker
canonicalExactBlockers =
  canonicalCellQuadratureBlockerReceipt
  ∷ canonicalSmoothingApproximationBlockerReceipt
  ∷ canonicalHolonomySamplingBlockerReceipt
  ∷ canonicalRenormalizedInnerProductBlockerReceipt
  ∷ canonicalAdjointnessResidualBlockerReceipt
  ∷ canonicalApproximateInverseBlockerReceipt
  ∷ canonicalNonPromotionBlockerReceipt
  ∷ []

canonicalBlockerLedger : BlockerLedger
canonicalBlockerLedger =
  mkBlockerLedger
    exact-fail-closed-blocker-lane
    exactCellQuadratureBlockerText
    exactSmoothingBlockerText
    exactHolonomySamplingBlockerText
    exactRenormalizedInnerProductBlockerText
    exactAdjointnessResidualBlockerText
    exactApproximateInverseBlockerText
    nonPromotionBoundaryText
    canonicalExactBlockers
    (exactCellQuadratureBlockerText
     ∷ exactSmoothingBlockerText
     ∷ exactHolonomySamplingBlockerText
     ∷ exactRenormalizedInnerProductBlockerText
     ∷ exactAdjointnessResidualBlockerText
     ∷ exactApproximateInverseBlockerText
     ∷ nonPromotionBoundaryText
     ∷ [])
    failClosedBlockersRecorded
    exact-fail-closed-blocker

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    receipt-lane
    nonPromotionBoundaryText
    cellQuadratureConvergenceProvedHere
    refl
    smoothingApproximationConvergenceProvedHere
    refl
    holonomySamplingConvergenceProvedHere
    refl
    renormalizedInnerProductConvergenceProvedHere
    refl
    adjointnessResidualVanishesProvedHere
    refl
    quadratureResidualTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint113QuadratureResidualEstimateReceipt :
  YMSprint113QuadratureResidualEstimateReceipt
canonicalYMSprint113QuadratureResidualEstimateReceipt =
  mkYMSprint113QuadratureResidualEstimateReceipt
    sprintNumber
    modulePath
    canonicalSprint112Inputs
    canonicalCellQuadratureEstimate
    canonicalSmoothingApproximationEstimate
    canonicalHolonomySamplingErrorEstimate
    canonicalRenormalizedInnerProductComparison
    canonicalAdjointnessResidualTarget
    canonicalBlockerLedger
    canonicalTheoremBoundary
    canonicalResidualLanes
    canonicalResidualComponents
    (cellQuadratureEstimateText
     ∷ smoothingApproximationEstimateText
     ∷ holonomySamplingErrorEstimateText
     ∷ renormalizedInnerProductComparisonText
     ∷ adjointnessResidualTargetText
     ∷ exactCellQuadratureBlockerText
     ∷ exactSmoothingBlockerText
     ∷ exactHolonomySamplingBlockerText
     ∷ exactRenormalizedInnerProductBlockerText
     ∷ exactAdjointnessResidualBlockerText
     ∷ exactApproximateInverseBlockerText
     ∷ nonPromotionBoundaryText
     ∷ [])
    quadratureResidualEstimateRecorded
    failClosedBlockersRecorded
    quadratureResidualTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt : YMSprint113QuadratureResidualEstimateReceipt
canonicalReceipt =
  canonicalYMSprint113QuadratureResidualEstimateReceipt

canonicalCellQuadratureConvergenceProvedHereIsFalse :
  TheoremBoundary.cellQuadratureConvergenceProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCellQuadratureConvergenceProvedHereIsFalse =
  refl

canonicalSmoothingApproximationConvergenceProvedHereIsFalse :
  TheoremBoundary.smoothingApproximationConvergenceProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalSmoothingApproximationConvergenceProvedHereIsFalse =
  refl

canonicalHolonomySamplingConvergenceProvedHereIsFalse :
  TheoremBoundary.holonomySamplingConvergenceProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalHolonomySamplingConvergenceProvedHereIsFalse =
  refl

canonicalRenormalizedInnerProductConvergenceProvedHereIsFalse :
  TheoremBoundary.renormalizedInnerProductConvergenceProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalRenormalizedInnerProductConvergenceProvedHereIsFalse =
  refl

canonicalAdjointnessResidualVanishesProvedHereIsFalse :
  TheoremBoundary.adjointnessResidualVanishesProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalAdjointnessResidualVanishesProvedHereIsFalse =
  refl

canonicalQuadratureResidualTheoremProvedHereIsFalse :
  quadratureResidualTheoremProvedHereReceipt canonicalReceipt ≡ false
canonicalQuadratureResidualTheoremProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptAdjointnessTarget : AdjointnessResidualTarget
canonicalReceiptAdjointnessTarget =
  adjointnessResidualTarget canonicalReceipt

canonicalReceiptExactBlockers : List ExactFailClosedBlocker
canonicalReceiptExactBlockers =
  exactBlockers (blockers canonicalReceipt)

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
