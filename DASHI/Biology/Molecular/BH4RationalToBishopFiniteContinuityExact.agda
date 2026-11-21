module DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact where

-- P0 source-preserving rational-to-Bishop-real finite continuity lift.
-- Every sum and species weight is explicit. Source conservation must be
-- supplied independently from the actual original 29x12 / 54-bond owner.
-- This module neither invents Rhea coefficients nor source rates.
-- Rational equality implies Bishop setoid equality, not definitional
-- equality of distinct Bishop Cauchy-real representatives.
--
-- Earlier Bishop real embedding/distributivity and 369 geometry are
-- reused prior work; this is finite indexed proof integration.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as Fin
import Data.Rational.Unnormalised as Q
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

rationalFiniteSum : ∀ {n} → V.Vec Q.ℚᵘ n → Q.ℚᵘ
rationalFiniteSum V.[] = Q.0ℚᵘ
rationalFiniteSum (V._∷_ a rest) =
  Q._+_ a (rationalFiniteSum rest)

bishopFiniteSum : ∀ {n} → V.Vec R.ℝ n → R.ℝ
bishopFiniteSum V.[] = Embed.embed Q.0ℚᵘ
bishopFiniteSum (V._∷_ a rest) =
  R._+_ a (bishopFiniteSum rest)

-- The original rational finite sum and the real-image finite sum
-- agree at every dimension, with no limiting or decimal operation.
rationalFiniteSumEmbeds :
  ∀ {n} (values : V.Vec Q.ℚᵘ n) →
  R._≃_
    (Embed.embed (rationalFiniteSum values))
    (bishopFiniteSum (V.map Embed.embed values))
rationalFiniteSumEmbeds V.[] = RP.≃-refl
rationalFiniteSumEmbeds (V._∷_ a rest) =
  RP.≃-trans
    (RP.⋆-distrib-+ a (rationalFiniteSum rest))
    (RP.+-cong RP.≃-refl (rationalFiniteSumEmbeds rest))

rationalZeroSumEmbeds :
  ∀ {n} (values : V.Vec Q.ℚᵘ n) →
  Q._≃_ (rationalFiniteSum values) Q.0ℚᵘ →
  R._≃_
    (bishopFiniteSum (V.map Embed.embed values))
    (Embed.embed Q.0ℚᵘ)
rationalZeroSumEmbeds values zeroProof =
  RP.≃-trans
    (RP.≃-symm (rationalFiniteSumEmbeds values))
    (RP.⋆-cong zeroProof)

-- Explicit source-weighted 29-species dot product.
sourceWeightedRow :
  ∀ {n} → V.Vec Q.ℚᵘ n → V.Vec Q.ℚᵘ n → Q.ℚᵘ
sourceWeightedRow V.[] V.[] = Q.0ℚᵘ
sourceWeightedRow (V._∷_ weight weights) (V._∷_ value values) =
  Q._+_ (Q._*_ weight value) (sourceWeightedRow weights values)

bishopWeightedRow :
  ∀ {n} → V.Vec R.ℝ n → V.Vec R.ℝ n → R.ℝ
bishopWeightedRow V.[] V.[] = Embed.embed Q.0ℚᵘ
bishopWeightedRow (V._∷_ weight weights) (V._∷_ value values) =
  R._+_ (R._*_ weight value) (bishopWeightedRow weights values)

weightedRowEmbeds :
  ∀ {n} (weights values : V.Vec Q.ℚᵘ n) →
  R._≃_
    (Embed.embed (sourceWeightedRow weights values))
    (bishopWeightedRow
      (V.map Embed.embed weights) (V.map Embed.embed values))
weightedRowEmbeds V.[] V.[] = RP.≃-refl
weightedRowEmbeds (V._∷_ w weights) (V._∷_ v values) =
  RP.≃-trans
    (RP.⋆-distrib-+ (Q._*_ w v) (sourceWeightedRow weights values))
    (RP.+-cong
      (RP.⋆-distrib-* w v)
      (weightedRowEmbeds weights values))

-- The 27 native voxels are the original accounting chart, not a
-- replacement for the semantic 369/pants spatial geometry.
sourceSpatialWeighted :
  ∀ {sites} → V.Vec Q.ℚᵘ 29 →
  V.Vec (V.Vec Q.ℚᵘ 29) sites → Q.ℚᵘ
sourceSpatialWeighted weights V.[] = Q.0ℚᵘ
sourceSpatialWeighted weights (V._∷_ row rest) =
  Q._+_ (sourceWeightedRow weights row)
         (sourceSpatialWeighted weights rest)

bishopSpatialWeighted :
  ∀ {sites} → V.Vec R.ℝ 29 →
  V.Vec (V.Vec R.ℝ 29) sites → R.ℝ
bishopSpatialWeighted weights V.[] = Embed.embed Q.0ℚᵘ
bishopSpatialWeighted weights (V._∷_ row rest) =
  R._+_ (bishopWeightedRow weights row)
         (bishopSpatialWeighted weights rest)

spatialWeightedEmbeds :
  ∀ {sites} (weights : V.Vec Q.ℚᵘ 29)
    (rhs : V.Vec (V.Vec Q.ℚᵘ 29) sites) →
  R._≃_
    (Embed.embed (sourceSpatialWeighted weights rhs))
    (bishopSpatialWeighted
      (V.map Embed.embed weights)
      (V.map (V.map Embed.embed) rhs))
spatialWeightedEmbeds weights V.[] = RP.≃-refl
spatialWeightedEmbeds weights (V._∷_ row rest) =
  RP.≃-trans
    (RP.⋆-distrib-+
      (sourceWeightedRow weights row)
      (sourceSpatialWeighted weights rest))
    (RP.+-cong
      (weightedRowEmbeds weights row)
      (spatialWeightedEmbeds weights rest))

-- Same source-supplied rational 27x29 RHS and same source weights.
-- This is a genuine lift of an exact zero defect, not a claim that
-- synthetic SG currents are the original physiological currents.
original369RationalZeroDefectImpliesBishopZero :
  (weights : V.Vec Q.ℚᵘ 29)
  (rhs : V.Vec (V.Vec Q.ℚᵘ 29) 27) →
  Q._≃_ (sourceSpatialWeighted weights rhs) Q.0ℚᵘ →
  R._≃_
    (bishopSpatialWeighted
      (V.map Embed.embed weights)
      (V.map (V.map Embed.embed) rhs))
    (Embed.embed Q.0ℚᵘ)
original369RationalZeroDefectImpliesBishopZero weights rhs zeroDefect =
  RP.≃-trans
    (RP.≃-symm (spatialWeightedEmbeds weights rhs))
    (RP.⋆-cong zeroDefect)

-- Six source-checked CHNOP/z conservation inputs are kept as one
-- source-matched six-axis object, not fabricated as distinct rates.
original369SixRationalConservationLiftsToBishop :
  (weights : V.Vec (V.Vec Q.ℚᵘ 29) 6)
  (rhs : V.Vec (V.Vec Q.ℚᵘ 29) 27) →
  ((axis : Fin.Fin 6) →
    Q._≃_ (sourceSpatialWeighted (V.lookup weights axis) rhs) Q.0ℚᵘ) →
  (axis : Fin.Fin 6) →
  R._≃_
    (bishopSpatialWeighted
      (V.map Embed.embed (V.lookup weights axis))
      (V.map (V.map Embed.embed) rhs))
    (Embed.embed Q.0ℚᵘ)
original369SixRationalConservationLiftsToBishop weights rhs exact axis =
  original369RationalZeroDefectImpliesBishopZero
    (V.lookup weights axis) rhs (exact axis)
