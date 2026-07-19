module DASHI.Analysis.FiniteOperatorReductionCore where

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
  ; covariance
  ; average
  ; averageStar
  ; middleInverse
  ; middleInverseLeft
  ; constrainedMinimizer
  ; constrainedMinimizerHasAverage
  ; KernelProjectionData
  ; minimizerData
  ; fineSubtract
  ; coarseSubtract
  ; coarseZero
  ; averageSubtract
  ; coarseSubtractSelf
  ; kernelProjection
  ; kernelProjectionHasZeroAverage
  ; FiniteHessianCertificate
  ; hessian
  ; inner
  ; symmetric
  ; Positive
  ; positive
  ; FiniteCovarianceCertificate
  ; covarianceLeft
  ; covarianceRight
  ; BlockSchurData
  ; aBlock
  ; bBlock
  ; cBlock
  ; dBlock
  ; aInverse
  ; add
  ; subtract
  ; compose
  ; schurComplement
  ; schurDefinition
  ; determinant
  ; scalarMultiply
  ; determinantFactorization
  ; FiniteContractionCertificate
  ; step
  ; distance
  ; StrictlySmaller
  ; fixedPoint
  ; fixed
  ; contractive
  )

open import DASHI.Analysis.BlockSchurCoercivity public

open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedBlockHodgePoincare public using
  ( OrderedEnergy
  ; _≤_
  ; add
  ; reflexive
  ; transitive
  ; addMonotoneRight
  ; gaugeFixedEnergy
  ; blockHodgePoincareFromLocal
  ; GaugeFixedBlockHodgePoincare
  ; normSquared
  ; curlEnergy
  ; divergenceEnergy
  ; averageEnergy
  ; constantWeightedEnergy
  ; weightedEnergyDefinition
  ; hodgePoincare
  ; ZeroBackgroundCoercivity
  ; hessianEnergy
  ; coercive
  ; hodgePoincareGivesZeroBackgroundCoercivity
  ; backgroundCoercivityFromPerturbation
  )
