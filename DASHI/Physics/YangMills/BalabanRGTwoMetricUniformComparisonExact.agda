module DASHI.Physics.YangMills.BalabanRGTwoMetricUniformComparisonExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION
--
-- Repository-local precursors:
--   * PR #530: an actual stroboscopic contraction on the 369 ultrametric;
--   * PR #525/#558: address-wheel isometry versus depth-wheel dynamics;
--   * BalabanPhysicalClusteringScaleAlgebraExact: lattice/physical scale
--     conversion already kept explicit in the Yang--Mills lane.
--
-- DASHI CONTRIBUTION
--
-- RG-depth contraction and physical-metric contraction are different
-- statements.  This file proves the exact division-free transport theorem
-- which is needed before any scale-coordinate contraction can be promoted to
-- a physical one.
--
-- If
--   c_- d_phys' <= a d_RG'
--   d_RG' <= lambda d_RG + epsilon
--   a d_RG <= c_+ d_phys
-- with a,lambda >= 0, then
--   c_- d_phys' <= lambda c_+ d_phys + a epsilon.
--
-- Thus a beautiful contraction in an RG/refinement metric is useless for a
-- continuum mass-gap claim unless c_-, c_+ and the normalization a are
-- controlled uniformly in the cutoff and the physical error is summable.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record RGTwoMetricStep : Set where
  field
    physicalScale : ℚ
    contraction : ℚ
    comparisonLower comparisonUpper : ℚ

    rgDistance rgDistanceNext : ℚ
    physicalDistance physicalDistanceNext : ℚ
    reopeningError : ℚ

    physicalScaleNonnegative : 0ℚ ≤ physicalScale
    contractionNonnegative : 0ℚ ≤ contraction

    lowerComparison :
      comparisonLower * physicalDistanceNext
      ≤ physicalScale * rgDistanceNext

    rgContractionWithResidual :
      rgDistanceNext
      ≤ contraction * rgDistance + reopeningError

    upperComparison :
      physicalScale * rgDistance
      ≤ comparisonUpper * physicalDistance
open RGTwoMetricStep public

rgContractionTransfersToPhysicalMetric :
  ∀ step →
  comparisonLower step * physicalDistanceNext step
  ≤ contraction step * comparisonUpper step * physicalDistance step
    + physicalScale step * reopeningError step
rgContractionTransfersToPhysicalMetric step =
  let
    scaledContraction :
      physicalScale step * rgDistanceNext step
      ≤ physicalScale step
        * (contraction step * rgDistance step + reopeningError step)
    scaledContraction =
      Norm.scaleNonnegative
        (physicalScale step)
        (physicalScaleNonnegative step)
        (rgContractionWithResidual step)

    scaledUpper :
      contraction step * (physicalScale step * rgDistance step)
      ≤ contraction step * (comparisonUpper step * physicalDistance step)
    scaledUpper =
      Norm.scaleNonnegative
        (contraction step)
        (contractionNonnegative step)
        (upperComparison step)

    withResidual :
      contraction step * (physicalScale step * rgDistance step)
        + physicalScale step * reopeningError step
      ≤ contraction step * (comparisonUpper step * physicalDistance step)
        + physicalScale step * reopeningError step
    withResidual =
      ℚP.+-monoˡ-≤
        (physicalScale step * reopeningError step)
        scaledUpper

    middle :
      physicalScale step * rgDistanceNext step
      ≤ contraction step * comparisonUpper step * physicalDistance step
        + physicalScale step * reopeningError step
    middle =
      ℚP.≤-trans
        scaledContraction
        (subst
          (λ left →
            left
            ≤ contraction step * comparisonUpper step * physicalDistance step
              + physicalScale step * reopeningError step)
          (ℚRing.solve-∀
            (physicalScale step)
            (contraction step)
            (rgDistance step)
            (reopeningError step))
          (subst
            (λ right →
              contraction step * (physicalScale step * rgDistance step)
                + physicalScale step * reopeningError step
              ≤ right)
            (ℚRing.solve-∀
              (contraction step)
              (comparisonUpper step)
              (physicalDistance step)
              (physicalScale step)
              (reopeningError step))
            withResidual))
  in
  ℚP.≤-trans (lowerComparison step) middle

twoMetricPhysicalTransportLevel : ProofLevel
twoMetricPhysicalTransportLevel = machineChecked

-- Physical frontier: prove cutoff-independent positive c_- and finite c_+ for
-- the SAME metric normalization used by the RG step.  No theorem in Cheeger
-- theory supplies this cross-scale identification automatically.
cutoffUniformTwoMetricComparisonLevel : ProofLevel
cutoffUniformTwoMetricComparisonLevel = conditional

cutoffUniformPhysicalResidualSummabilityLevel : ProofLevel
cutoffUniformPhysicalResidualSummabilityLevel = conditional
