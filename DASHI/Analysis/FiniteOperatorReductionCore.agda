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
