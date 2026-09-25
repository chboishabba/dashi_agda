{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSameSystemGaussianWardKernelTheoremExact where

------------------------------------------------------------------------
-- H6 theorem-bearing constructor.
--
-- No OPE/stress carrier is introduced.  Under Gaussianity on the SAME
-- continuum Schwinger system, the physical theorem supplies the local
-- two-derivative Ward kernel consumed by the exact Maxwell classifier.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Exact as R563

literalSameSystemGaussianWardKernel :
  ∀ {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (Gaussian :
      OS.ContinuumSchwingerSystem Observable Point Scalar → Set)
    (coefficientAlgebra :
      Ward.WardCoefficientAdditiveGroup)
    (gaussianLocalTwoDerivativeWardKernel :
      Gaussian system →
      Ward.GenericLocalTwoDerivativeWardKernel coefficientAlgebra) →
  R563.SameFamilyWardKernelSource system
literalSameSystemGaussianWardKernel
    Gaussian coefficientAlgebra gaussianLocalTwoDerivativeWardKernel = record
  { R563.SameFamilyWardKernelSource.Gaussian = Gaussian
  ; R563.SameFamilyWardKernelSource.coefficientAlgebra =
      coefficientAlgebra
  ; R563.SameFamilyWardKernelSource.gaussianLocalTwoDerivativeWardKernel =
      gaussianLocalTwoDerivativeWardKernel
  }
