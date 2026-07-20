module DASHI.Analysis.FiniteOperatorReductionCore where

open import Agda.Primitive using (Level)

import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as Finite
import DASHI.Physics.YangMills.BalabanSU2GaugeFixedBlockHodgePoincare as Hodge

------------------------------------------------------------------------
-- Domain-neutral access to the finite operator kernels first developed in
-- the Bałaban one-step Yang–Mills lane.
--
-- The definitions themselves are mathematical rather than gauge-specific:
-- constrained minimizers, kernel projections, finite Hessian/covariance
-- certificates, Schur complements, contraction certificates, and
-- Hodge–Poincaré coercivity.  This module gives chemistry, biology, and other
-- physics lanes a stable analysis namespace without copying those kernels.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore public using
  ( ConstrainedMinimizerData
  ; constrainedMinimizer
  ; constrainedMinimizerHasAverage
  ; KernelProjectionData
  ; kernelProjection
  ; kernelProjectionHasZeroAverage
  ; FiniteHessianCertificate
  ; FiniteCovarianceCertificate
  ; BlockSchurData
  ; FiniteContractionCertificate
  )

open import DASHI.Analysis.BlockSchurCoercivity public

open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedBlockHodgePoincare public using
  ( OrderedEnergy
  ; gaugeFixedEnergy
  ; blockHodgePoincareFromLocal
  ; GaugeFixedBlockHodgePoincare
  ; ZeroBackgroundCoercivity
  ; hodgePoincareGivesZeroBackgroundCoercivity
  ; backgroundCoercivityFromPerturbation
  )

------------------------------------------------------------------------
-- Stable domain-neutral projection names.  These avoid forcing consumers to
-- know which original implementation module owns each generated record field.
------------------------------------------------------------------------

constraintAverage :
  ∀ {f c : Level}
    {Fine : Set f}
    {Coarse : Set c} →
  ConstrainedMinimizerData Fine Coarse →
  Fine → Coarse
constraintAverage = Finite.ConstrainedMinimizerData.average

orderedEnergyLeq :
  ∀ {s : Level}
    {Scalar : Set s} →
  OrderedEnergy Scalar →
  Scalar → Scalar → Set s
orderedEnergyLeq = Hodge.OrderedEnergy._≤_

hodgeNormSquared :
  ∀ {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    {order : OrderedEnergy Scalar} →
  GaugeFixedBlockHodgePoincare Vector Scalar order →
  Vector → Scalar
hodgeNormSquared = Hodge.GaugeFixedBlockHodgePoincare.normSquared

hodgeWeightedEnergy :
  ∀ {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    {order : OrderedEnergy Scalar} →
  GaugeFixedBlockHodgePoincare Vector Scalar order →
  Vector → Scalar
hodgeWeightedEnergy = Hodge.GaugeFixedBlockHodgePoincare.constantWeightedEnergy

hodgeControlsNorm :
  ∀ {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    {order : OrderedEnergy Scalar} →
  (H : GaugeFixedBlockHodgePoincare Vector Scalar order) →
  (vector : Vector) →
  orderedEnergyLeq order
    (hodgeNormSquared H vector)
    (hodgeWeightedEnergy H vector)
hodgeControlsNorm = Hodge.GaugeFixedBlockHodgePoincare.hodgePoincare
