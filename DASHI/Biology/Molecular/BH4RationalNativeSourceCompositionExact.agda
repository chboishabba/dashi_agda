module DASHI.Biology.Molecular.BH4RationalNativeSourceCompositionExact where

-- Producer-side composition of actual finite chart dimensions:
-- 6 source conservation axes, 29 molecular species, 12 gross original
-- reaction columns, 27 voxel rate rows, 54 native bond flux rows.
--
-- Unlike the previously consumer-only Bishop transport, NO six global
-- zero defects are assumed. They follow algebraically from *columnwise*
-- rational left-kernel equalities and paired native flux cancellation.
--
-- Open source seams: identify the rational sides with the Nat
-- SourceCertifiedOriginal29x12 original certificate, and identify
-- paired bond totals with the actual signed 27x54 divergence.
-- Original reaction rates/SG currents and a kernel run remain unpaid.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Embed

import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4RationalNativeBondCancellationExact as Native
import DASHI.Biology.Molecular.BH4RationalRateWeightedSourceConservationExact as Rates

-- One source axis's combined signed flux + gross reaction conservation.
-- This is stronger than requiring a zero-defect receipt: it derives
-- equality using only 12 individual rational source-column balances.
originalOneAxisNativeAndReactionBalance :
  (weights : V.Vec Q.ℚᵘ 29)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54) →
  ((column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow weights (V.lookup reactants column))
      (Lift.sourceWeightedRow weights (V.lookup products column))) →
  Q._≃_
    (Q._+_
      (Native.pairedNativeBondCollection weights fluxes)
      (Rates.spatialRateWeightedTotal weights reactants rates))
    (Rates.spatialRateWeightedTotal weights products rates)
originalOneAxisNativeAndReactionBalance
  weights reactants products rates fluxes columnBalanced =
  QP.≃-trans
    (QP.+-cong
      (Native.original54x29PairedNativeFluxCancels weights fluxes)
      (Rates.original369x29x12RationalRatesPreserveKernel
        weights reactants products rates columnBalanced))
    (QP.+-identityˡ
      (Rates.spatialRateWeightedTotal weights products rates))

-- All six original coordinates share exactly the same source reaction
-- sides, rate rows and flux rows; only the certified weight axis varies.
originalSixAxisNativeAndReactionBalance :
  (weights : V.Vec (V.Vec Q.ℚᵘ 29) 6)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54) →
  ((axis : F.Fin 6) (column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow (V.lookup weights axis)
        (V.lookup reactants column))
      (Lift.sourceWeightedRow (V.lookup weights axis)
        (V.lookup products column))) →
  (axis : F.Fin 6) →
  Q._≃_
    (Q._+_
      (Native.pairedNativeBondCollection
        (V.lookup weights axis) fluxes)
      (Rates.spatialRateWeightedTotal
        (V.lookup weights axis) reactants rates))
    (Rates.spatialRateWeightedTotal
      (V.lookup weights axis) products rates)
originalSixAxisNativeAndReactionBalance
  weights reactants products rates fluxes balanced axis =
  originalOneAxisNativeAndReactionBalance
    (V.lookup weights axis) reactants products rates fluxes
    (balanced axis)

-- The same producer result is a Bishop setoid equality by the
-- established rational embedding. No independently asserted
-- 27x29 global-zero-defect witness is a parameter.
originalSixAxisNativeReactionBalanceBishop :
  (weights : V.Vec (V.Vec Q.ℚᵘ 29) 6)
  (reactants products : V.Vec (V.Vec Q.ℚᵘ 29) 12)
  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)
  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54) →
  ((axis : F.Fin 6) (column : F.Fin 12) →
    Q._≃_
      (Lift.sourceWeightedRow (V.lookup weights axis)
        (V.lookup reactants column))
      (Lift.sourceWeightedRow (V.lookup weights axis)
        (V.lookup products column))) →
  (axis : F.Fin 6) →
  R._≃_
    (Embed.embed
      (Q._+_
        (Native.pairedNativeBondCollection
          (V.lookup weights axis) fluxes)
        (Rates.spatialRateWeightedTotal
          (V.lookup weights axis) reactants rates)))
    (Embed.embed
      (Rates.spatialRateWeightedTotal
        (V.lookup weights axis) products rates))
originalSixAxisNativeReactionBalanceBishop
  weights reactants products rates fluxes balanced axis =
  RP.⋆-cong
    (originalSixAxisNativeAndReactionBalance
      weights reactants products rates fluxes balanced axis)
