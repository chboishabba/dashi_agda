module DASHI.Analysis.BishopStrictRatioInterpolationExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE STRICT RATIO INTERPOLATION ON BISHOP REALS
--
-- SOURCE / ATTRIBUTION
--
-- The pinned Murray/Bishop constructive-real library proves density of the
-- rationals in the reals:
--
--   fast-density-of-ℚ :
--     x < y -> Σ ℚᵘ (λ α -> x < α⋆ < y).
--
-- DASHI CONTRIBUTION
--
-- Specialize that theorem to 0 <= r < 1.  The resulting larger ratio is an
-- embedded rational and therefore provides the exact constructive witness
-- required by polynomial/geometric absorption:
--
--   0 < ρ,  r < ρ < 1.
--
-- No choice principle or new Archimedean/order postulate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel

interpolateStrictUnitRatio :
  ∀ {ratio : BishopReal.ℝ} →
  BishopReal._≤_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  Σ BishopReal.ℝ (λ larger →
    BishopReal._<_ BishopReal.0ℝ larger ×
    BishopReal._<_ ratio larger ×
    BishopReal._<_ larger BishopReal.1ℝ)
interpolateStrictUnitRatio {ratio} ratioNonnegative ratioBelowOne
  with BishopP.fast-density-of-ℚ ratio BishopReal.1ℝ ratioBelowOne
... | rational , ratioBelowLarger , largerBelowOne =
  BishopReal._⋆ rational ,
  BishopP.≤-<-trans ratioNonnegative ratioBelowLarger ,
  ratioBelowLarger ,
  largerBelowOne

bishopStrictRatioInterpolationLevel : ProofLevel
bishopStrictRatioInterpolationLevel = conditional
