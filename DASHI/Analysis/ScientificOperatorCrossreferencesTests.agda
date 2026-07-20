module DASHI.Analysis.ScientificOperatorCrossreferencesTests where

------------------------------------------------------------------------
-- This focused regression surface checks that the cross-domain modules share
-- the intended theorem-bearing analysis types.  Concrete physical and chemical
-- instances remain downstream obligations.
------------------------------------------------------------------------

open import DASHI.Analysis.FiniteOperatorReductionCore
open import DASHI.Physics.Chemistry.AtomicClosedShellSchurBridge
open import DASHI.Biology.Molecular.MolecularConstrainedMinimizerBridge
open import DASHI.Biology.Morphogenesis.ReactionDiffusionHodgeBridge

constrainedMinimizerKernelAvailable : Set₁
constrainedMinimizerKernelAvailable =
  ∀ {Fine Coarse : Set} → ConstrainedMinimizerData Fine Coarse → Coarse → Fine

quantitativeSchurKernelAvailable : Set₁
quantitativeSchurKernelAvailable =
  ∀ {Vector Scalar : Set}
    (O : SchurOrderLaws Scalar) →
    QuantitativeBlockSchur Vector Scalar O →
    Set

hodgePoincareKernelAvailable : Set₁
hodgePoincareKernelAvailable =
  ∀ {Vector Scalar : Set}
    (O : OrderedEnergy Scalar) →
    GaugeFixedBlockHodgePoincare Vector Scalar O →
    Set
