module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicExponentialExact where

------------------------------------------------------------------------
-- FACTOR-PAIR EXPONENTIAL DOMINATION
--
-- For r=k*v, use v cubic translations with step k*x_n.  The factor-pair
-- residual owner proves the resulting translated exponent stays below the
-- target c*sqrt(n), while concrete exponential monotonicity closes the final
-- comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact as ExpMono
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorPairCubicExponentialDomination :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  r ≤ n →
  (pair : Factor.PositiveFactorPair r) →
  let rate = Rate.canonicalErdosStepRate n nPositive
      factorPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._≤_
    (Exp.bishopExp (Rate.residualExponent n r))
    (BishopReal._*_
      (Iterated.powerQ factorPositive (Factor.divisor pair))
      (Exp.bishopExp (Rate.targetExponent n)))
factorPairCubicExponentialDomination {n} {r} nPositive r≤n pair =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    factorPositive = FactorResidual.factorStepPositive rate pair
    residualNN = Rate.residualExponentNonnegative n r
    factorNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx factorPositive)
    shiftedNN =
      Iterated.shiftedBaseNonnegative residualNN factorNN (Factor.divisor pair)

    iterated =
      Iterated.iteratedCubicTranslation
        residualNN factorPositive (Factor.divisor pair)

    exponentOrder =
      ExpMono.bishopExpMonotoneNonnegative
        shiftedNN
        (FactorResidual.factorShiftedResidualBelowTarget nPositive r≤n pair)

    scaledExponentOrder =
      BishopP.*-monoˡ-≤-nonNeg
        exponentOrder
        (Iterated.powerQNonnegative factorPositive (Factor.divisor pair))
  in
  BishopP.≤-trans iterated scaledExponentOrder

partitionErdosBishopFactorPairCubicExponentialLevel : ProofLevel
partitionErdosBishopFactorPairCubicExponentialLevel = machineChecked
