module DASHI.Moonshine.AbelBishopLogUpperDiskSetoidZeroExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG(1+w): ZERO NORMALIZATION FOR EVERY w ≈C 0.
--
-- At the selected p-chart centre, u = p^-1 * 0 is SETOID equal to
-- zero, not necessarily propositionally equal to zero. The old
-- log(1)=0 lemma only stated the result at the literal complex zero.
--
-- Here source termwise setoid congruence, finite real/imaginary
-- series extensionality, the original zero-series convergence and
-- the original Bishop series limit uniqueness show:
--
--   w ≈C 0 => logSeriesUpperDisk(w) ≈C 0.
--
-- This is an ACTUAL source normalization weld and does not invent
-- a principal log inverse, global Koenigs map or analytic inequality.
-- Native Agda 2.9 kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopLogOnePlusZeroNormalizationExact as Zero
import DASHI.Moonshine.AbelBishopLogOnePlusUpperDiskConvergenceExact as UpperLog
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Ring

-- The original normalized local displacement vanishes at t=0 in the
-- Bishop complex SETOID, using the already-proved right-zero law.
originalBishopNormalizedDisplacementAtZero :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) →
  Complex._≈C_
    (Affine.normalizedDisplacement p nz Algebra.zeroC)
    Algebra.zeroC
originalBishopNormalizedDisplacementAtZero p nz =
  Laws.complexMultiplyRightZero (Reciprocal.reciprocalC p nz)

-- Move the known literal ZERO coefficient-series convergence to ANY
-- setoid-equal input. This is not a continuity or principal-log axiom.
originalBishopLogZeroSeriesConvergesAtEquivalent :
  ∀ {w} →
  Complex._≈C_ w Algebra.zeroC →
  Complex.ComplexSeriesConvergesTo
    (Log.originalBishopLogOnePlusTerm w)
    Algebra.zeroC
originalBishopLogZeroSeriesConvergesAtEquivalent {w} equivalent =
  Complex.complex-series-converges-to
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        BishopP.≃-symm
          (Ext.seriesPartialSumsCongruent
            (λ k → proj₁
              (Log.originalBishopLogOnePlusTermCongruent equivalent k))
            n))
      (Complex.realConverges Zero.originalBishopLogZeroSeriesConverges))
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        BishopP.≃-symm
          (Ext.seriesPartialSumsCongruent
            (λ k → proj₂
              (Log.originalBishopLogOnePlusTermCongruent equivalent k))
            n))
      (Complex.imagConverges Zero.originalBishopLogZeroSeriesConverges))

originalBishopUpperDiskLogZeroFromSetoidZero :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Complex._≈C_ w Algebra.zeroC →
  Complex._≈C_
    (UpperLog.originalBishopLogUpperDiskCanonicalValue interval disk)
    Algebra.zeroC
originalBishopUpperDiskLogZeroFromSetoidZero {w}
  interval disk equivalent =
  Log.originalBishopLogOnePlusSeriesLimitUnique
    w
    (UpperLog.originalBishopLogUpperDiskAbsoluteConvergence
      interval disk)
    Algebra.zeroC
    (originalBishopLogZeroSeriesConvergesAtEquivalent equivalent)

originalBishopSelectedUpperDiskLogCenterNormalization :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p)
    {ratio}
    (interval : Unit.BishopUnitIntervalRatio ratio)
    (disk : Upper.BishopComplexNormSquareUpperRadius
      (Affine.normalizedDisplacement p nz Algebra.zeroC) ratio) →
  Complex._≈C_
    (Algebra._+C_ p
      (UpperLog.originalBishopLogUpperDiskCanonicalValue
        interval disk))
    p
originalBishopSelectedUpperDiskLogCenterNormalization
    p nz interval disk =
  Ring.complexTrans
    (Algebra.addCCongruent
      (Complex.≈C-refl p)
      (originalBishopUpperDiskLogZeroFromSetoidZero
        interval disk
        (originalBishopNormalizedDisplacementAtZero p nz)))
    (Laws.complexAddRightIdentity p)
