module DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicResidualExponentialExact where

------------------------------------------------------------------------
-- ERDOS RESIDUAL EXPONENTIAL DOMINATION
--
-- For positive n and r<=n, the shared step-rate owner gives
--
--   shiftedBase(c sqrt(n-r), x_n, r) <= c sqrt(n),
--
-- where x_n=c/(2sqrt(n)).  Iterated cubic translation gives
--
--   exp(c sqrt(n-r))
--     <= q_n^r * exp(shiftedBase(...)).
--
-- Monotonicity of the concrete Bishop exponential on nonnegative inputs then
-- yields
--
--   exp(c sqrt(n-r)) <= q_n^r * exp(c sqrt(n)).
--
-- No exp-additivity is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact as ExpMono
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
open import DASHI.Physics.YangMills.CompactLieProofLevel

residualExponential : Nat → Nat → BishopReal.ℝ
residualExponential n r = Exp.bishopExp (Rate.residualExponent n r)

targetExponential : Nat → BishopReal.ℝ
targetExponential n = Exp.bishopExp (Rate.targetExponent n)

cubicResidualExponentialDomination :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  r ≤ n →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (residualExponential n r)
    (BishopReal._*_
      (Iterated.powerQ (Rate.stepPositive rate) r)
      (targetExponential n))
cubicResidualExponentialDomination {n} {r} nPositive r≤n =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    xPositive = Rate.stepPositive rate
    residualNN = Rate.residualExponentNonnegative n r
    xNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive)
    shiftedNN =
      Iterated.shiftedBaseNonnegative residualNN xNN r

    iterated =
      Iterated.iteratedCubicTranslation
        residualNN xPositive r

    exponentOrder =
      ExpMono.bishopExpMonotoneNonnegative
        shiftedNN
        (Rate.shiftedResidualBelowTarget nPositive r≤n)

    scaledExponentOrder =
      BishopP.*-monoˡ-≤-nonNeg
        exponentOrder
        (Iterated.powerQNonnegative xPositive r)
  in
  BishopP.≤-trans iterated scaledExponentOrder

partitionErdosBishopCubicResidualExponentialLevel : ProofLevel
partitionErdosBishopCubicResidualExponentialLevel = machineChecked
