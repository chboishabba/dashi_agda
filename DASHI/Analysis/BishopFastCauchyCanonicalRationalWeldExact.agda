module DASHI.Analysis.BishopFastCauchyCanonicalRationalWeldExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP UNNORMALISED ℚᵘ -> ORIGINAL FASTCAUCHY REDUCED ℚ.
--
-- The FastCauchy canonical metric uses Data.Rational.Base.ℚ,
-- whereas Murray/Csimma Bishop real embedding uses ℚᵘ.
-- A naive claim that the two rational sequences are definitionally
-- identical is therefore FALSE at the representation level.
--
-- DASHI contribution: instantiate the actual reduced-rational constant
-- FastCauchy representative via Data.Rational.Base.fromℚᵘ.
-- The rational-image comparison with the canonical Bishop/Fast
-- equivalence is still a real proof obligation, not an axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; fromℚᵘ)
open import Data.Rational.Unnormalised using (ℚᵘ)

import Real as BishopReal
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as FastBackend
import DASHI.Analysis.BishopFastCauchyCategoricityInstanceExact as Canonical
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.BishopSetoidWeldExact as Weld
import DASHI.Analysis.BishopFastCauchyZetaWeldExact as ZetaWeld

canonicalFastFromBishopRational :
  ℚᵘ → Fast.FastCauchyReal Metric.canonicalRationalMetricAuthority
canonicalFastFromBishopRational q =
  Metric.canonicalRationalEmbedding (ℚ.fromℚᵘ q)

-- Literal normalised rational term at every FastCauchy index.
canonicalFastRationalTerm :
  (q : ℚᵘ) (n : Nat) →
  Fast.approximate (canonicalFastFromBishopRational q) n ≡
  ℚ.fromℚᵘ q
canonicalFastRationalTerm q n = refl

module _
    {operations :
      Fast.FastCauchyOperations Metric.canonicalRationalMetricAuthority}
    {bishopPackaging : Bishop.BishopAlgebraOrderPackaging}
    {fastPackaging :
      FastBackend.FastCauchyBackendPackaging
        Metric.canonicalRationalMetricAuthority operations}
    (dataSet : Canonical.BishopFastCauchyCategoricityData
      Metric.canonicalRationalMetricAuthority
      operations bishopPackaging fastPackaging)
  where

  -- The only missing rational bridge is now the equality of the
  -- generated canonical Bishop->Fast map on literal rational casts.
  -- No arbitrary 'fastRational' function remains.
  canonicalRationalWeld :
    ((q : ℚᵘ) →
      Fast._≈R_
        (Spine.map
          (Spine.toRight
            (Canonical.bishopFastCauchyCanonicalEquivalence dataSet))
          (BishopReal._⋆ q))
        (canonicalFastFromBishopRational q)) →
    Weld.RationalSetoidWeld
      (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
      (FastBackend.fastCauchySetoidOrderedCompleteReal
        operations fastPackaging)
  canonicalRationalWeld agreement =
    ZetaWeld.makeRationalWeld dataSet
      canonicalFastFromBishopRational agreement
