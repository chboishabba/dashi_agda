module DASHI.Moonshine.AbelBishopLogUpperDiskZeroNormalizationExact where

------------------------------------------------------------------------
-- ORIGINAL UPPER-DISK CANONICAL LOG SERIES AGREES WITH LOG(1)=0.
--
-- Previous owner AbelBishopLogOnePlusZeroNormalizationExact already
-- constructs the original ZERO-stream partial sums and proves their
-- convergence to zero. UpperDiskConvergence now constructs a SECOND
-- absolute convergence receipt at zero from ANY admissible upper
-- radius. Both receipts refer to the EXACT SAME original coefficient
-- stream, so uniqueness of the vendored Bishop series limit
-- identifies the original upper-disk canonical log(1) with zero.
--
-- No equality of distinct real carriers, synthetic principal branch
-- or exp-log inverse law is assumed here. Agda kernel pending.
------------------------------------------------------------------------

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopLogOnePlusZeroNormalizationExact as Zero
import DASHI.Moonshine.AbelBishopLogOnePlusUpperDiskConvergenceExact as UpperLog

originalBishopUpperDiskCanonicalLogOneIsZero :
  ∀ {ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius
    Algebra.zeroC ratio) →
  Complex._≈C_
    (UpperLog.originalBishopLogUpperDiskCanonicalValue interval disk)
    Algebra.zeroC
originalBishopUpperDiskCanonicalLogOneIsZero interval disk =
  Log.originalBishopLogOnePlusSeriesLimitUnique
    Algebra.zeroC
    (UpperLog.originalBishopLogUpperDiskAbsoluteConvergence
      interval disk)
    Algebra.zeroC
    Zero.originalBishopLogZeroSeriesConverges
