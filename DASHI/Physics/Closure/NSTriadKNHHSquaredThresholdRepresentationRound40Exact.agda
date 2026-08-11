module DASHI.Physics.Closure.NSTriadKNHHSquaredThresholdRepresentationRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Make explicit the change of variable used by the exact Round-40 threshold
-- optimizer.  The optimizer works with a positive rational scale r, while the
-- physical directional classifier uses delta.  A squared representation owns
-- both positive thresholds and proves
--
--   delta = r^2,
--   delta^{-1} = r^{-2}.
--
-- Therefore the analytic tax
--
--   A r + B r^{-2}
--
-- is literally
--
--   A sqrt(delta) + B/delta
--
-- without introducing a square-root primitive.  No physical constants are
-- invented: the representation is only a same-object bridge between the
-- classifier and the optimizer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact as Opt

record SquaredDirectionalThreshold : Set where
  field
    scale : Threshold.PositiveThreshold
    directionalParameter : Threshold.PositiveThreshold

    deltaIsScaleSquared :
      Threshold.threshold directionalParameter
      ≡ Threshold.threshold scale * Threshold.threshold scale

    inverseDeltaIsInverseScaleSquared :
      Threshold.thresholdInverse directionalParameter
      ≡ Threshold.thresholdInverse scale * Threshold.thresholdInverse scale

open SquaredDirectionalThreshold public

physicalGoodTaxAtSquaredThreshold :
  ℚ → SquaredDirectionalThreshold → ℚ
physicalGoodTaxAtSquaredThreshold A representation =
  Opt.hhGoodTax A (scale representation)

physicalBadTaxAtSquaredThreshold :
  ℚ → SquaredDirectionalThreshold → ℚ
physicalBadTaxAtSquaredThreshold B representation =
  Opt.hhBadTax B (scale representation)

badTaxUsesLiteralDeltaInverse :
  ∀ B representation →
  physicalBadTaxAtSquaredThreshold B representation
  ≡ B * Threshold.thresholdInverse
      (directionalParameter representation)
badTaxUsesLiteralDeltaInverse B representation
  rewrite inverseDeltaIsInverseScaleSquared representation = refl

goodSquaredThresholdMeaning :
  ∀ A representation →
  Opt.hhGoodTax A (scale representation)
    * Opt.hhGoodTax A (scale representation)
  ≡
  (A * A)
    * Threshold.threshold (directionalParameter representation)
goodSquaredThresholdMeaning A representation
  rewrite deltaIsScaleSquared representation =
  Data.Rational.Tactic.RingSolver.solve
    (A ∷ Threshold.threshold (scale representation) ∷ [])
  where
  open import Agda.Builtin.List using ([]; _∷_)
  import Data.Rational.Tactic.RingSolver

hhSquaredThresholdRepresentationTyped : Bool
hhSquaredThresholdRepresentationTyped = true

physicalSquaredDirectionalThresholdConstructed : Bool
physicalSquaredDirectionalThresholdConstructed = false

hhSquaredThresholdRepresentationTypedIsTrue :
  hhSquaredThresholdRepresentationTyped ≡ true
hhSquaredThresholdRepresentationTypedIsTrue = refl
