{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStochasticSpatialEnvelopeToConnectedClusteringRound258Exact where

------------------------------------------------------------------------
-- ROUND258 / STOCHASTIC SPATIAL ENVELOPE -> ROUND108 GEOMETRIC CLUSTERING
--
-- The older Round108 post-BC2 surface carries uniform geometric connected
-- clustering as a primitive physical record.  But Round70 already proves the
-- stochastic covariance-to-spatial-envelope step from:
--
--   * same-measure temporal relaxation at the balanced time;
--   * same-generator finite-speed propagation at the balanced time.
--
-- Therefore the remaining clustering seam is only the SHAPE of the selected
-- physical spatial envelope:
--
--     spatialEnvelope(F,G) <= A * q^(distance(F,G)),   0 <= q < 1.
--
-- Once that envelope shape is supplied, the Round108 clustering record is
-- compiler output.  No second stochastic covariance theorem is requested.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact as Stoch
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as R108

record RationalGeometricSpatialEnvelope (Observable : Set) : Set₁ where
  field
    stochastic : Stoch.StochasticFiniteSpeedClusteringData Observable ℚ

    -- The generic Round70 compiler keeps its order relation abstract.  This
    -- projection merely exposes that the selected physical instantiation uses
    -- the ordinary rational order; it is representation plumbing, not a new
    -- Yang--Mills estimate.
    lessEqualImpliesRational : ∀ {left right} →
      Stoch.LessEqual stochastic left right → left ≤ right

    amplitude ratio : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio
    ratioStrictlyBelowOne : ratio < 1ℚ

    -- The sole surviving clustering-shape payment on this route.
    spatialEnvelopeBelowGeometric : ∀ left right →
      Stoch.spatialEnvelope stochastic left right
      ≤ amplitude * Power.rationalPower ratio
          (Stoch.distance stochastic left right)

open RationalGeometricSpatialEnvelope public

connectedCovarianceBelowGeometric :
  ∀ {Observable}
    (dataSet : RationalGeometricSpatialEnvelope Observable)
    left right →
  Stoch.covariance (stochastic dataSet) left right
  ≤ amplitude dataSet * Power.rationalPower (ratio dataSet)
      (Stoch.distance (stochastic dataSet) left right)
connectedCovarianceBelowGeometric dataSet left right =
  ℚP.≤-trans
    (lessEqualImpliesRational dataSet
      (Stoch.spatialClusteringFromRelaxationAndFiniteSpeed
        (stochastic dataSet) left right))
    (spatialEnvelopeBelowGeometric dataSet left right)

asRound108UniformGeometricConnectedClustering :
  ∀ {Observable} →
  RationalGeometricSpatialEnvelope Observable →
  R108.UniformGeometricConnectedClustering Observable
asRound108UniformGeometricConnectedClustering dataSet = record
  { R108.UniformGeometricConnectedClustering.distance =
      Stoch.distance (stochastic dataSet)
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceMagnitude =
      Stoch.covariance (stochastic dataSet)
  ; R108.UniformGeometricConnectedClustering.amplitude = amplitude dataSet
  ; R108.UniformGeometricConnectedClustering.ratio = ratio dataSet
  ; R108.UniformGeometricConnectedClustering.amplitudeNonnegative =
      amplitudeNonnegative dataSet
  ; R108.UniformGeometricConnectedClustering.ratioNonnegative =
      ratioNonnegative dataSet
  ; R108.UniformGeometricConnectedClustering.ratioStrictlyBelowOne =
      ratioStrictlyBelowOne dataSet
  ; R108.UniformGeometricConnectedClustering.connectedCovarianceBound =
      connectedCovarianceBelowGeometric dataSet
  }

stochasticEnvelopeToRound108ClusteringCompilerLevel : ProofLevel
stochasticEnvelopeToRound108ClusteringCompilerLevel = machineChecked

-- The time optimization, covariance split and combination of temporal/finite-
-- speed pieces are already compiler-owned in Round70.  The remaining physical
-- clustering statement is only that the selected SAME-measure spatial envelope
-- is genuinely geometric/exponential in the physical distance.
literalSameFamilyGeometricSpatialEnvelopeLevel : ProofLevel
literalSameFamilyGeometricSpatialEnvelopeLevel = conditional
