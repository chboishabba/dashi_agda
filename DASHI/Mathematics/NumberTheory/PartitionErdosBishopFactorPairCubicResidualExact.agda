module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact where

------------------------------------------------------------------------
-- FACTOR-PAIR CUBIC RESIDUAL TRANSLATION
--
-- For a positive factor pair r = k*v, translate v times with step k*x_n.
-- The total repeated translation is exactly r*x_n, so the shared r-step
-- tangent bound from PartitionErdosBishopCubicStepRateExact applies.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorCopies : ∀ {r} → Factor.PositiveFactorPair r → Nat
factorCopies pair = suc (Factor.predecessor pair)

factorDivisor : ∀ {r} → Factor.PositiveFactorPair r → Nat
factorDivisor = Factor.divisor

factorStep :
  ∀ {n r} {nPositive : suc 0 ≤ n} →
  Rate.ErdosStepRate n nPositive →
  Factor.PositiveFactorPair r → BishopReal.ℝ
factorStep rate pair =
  Iterated.natScale (factorCopies pair) (Rate.step rate)

factorStepPositive :
  ∀ {n r} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._<_ BishopReal.0ℝ (factorStep rate pair)
factorStepPositive rate pair =
  BishopP.posx⇒0<x
    (Iterated.natScalePositiveSuccessor
      (BishopP.0<x⇒posx (Rate.stepPositive rate))
      (Factor.predecessor pair))

factorNestedScaleIsResidualScale :
  ∀ {n r} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (Iterated.natScale
      (factorDivisor pair)
      (factorStep rate pair))
    (Iterated.natScale r (Rate.step rate))
factorNestedScaleIsResidualScale rate pair =
  let
    k = factorCopies pair
    v = factorDivisor pair
    productReverse : v NatP.* k ≡ _
    productReverse =
      trans
        (NatP.*-comm v k)
        (sym (Factor.productExact pair))
  in
  BishopP.≃-trans
    (Iterated.nestedNatScaleProduct v k (Rate.step rate))
    (BishopP.≃-refl₂
      (cong
        (λ count → Iterated.natScale count (Rate.step rate))
        productReverse))

factorShiftedResidualEquivalentToResidualShift :
  ∀ {n r} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (Iterated.shiftedBase
      (Rate.residualExponent n r)
      (factorStep rate pair)
      (factorDivisor pair))
    (Iterated.shiftedBase
      (Rate.residualExponent n r)
      (Rate.step rate)
      r)
factorShiftedResidualEquivalentToResidualShift {n} {r} rate pair =
  BishopP.≃-trans
    (Iterated.shiftedBaseAsNatScale
      (Rate.residualExponent n r)
      (factorStep rate pair)
      (factorDivisor pair))
    (BishopP.≃-trans
      (BishopP.+-cong
        BishopP.≃-refl
        (factorNestedScaleIsResidualScale rate pair))
      (BishopP.≃-symm
        (Iterated.shiftedBaseAsNatScale
          (Rate.residualExponent n r)
          (Rate.step rate)
          r)))

factorShiftedResidualBelowTarget :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  r ≤ n →
  (pair : Factor.PositiveFactorPair r) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (Iterated.shiftedBase
      (Rate.residualExponent n r)
      (factorStep rate pair)
      (factorDivisor pair))
    (Rate.targetExponent n)
factorShiftedResidualBelowTarget {n} {r} nPositive r≤n pair =
  let rate = Rate.canonicalErdosStepRate n nPositive
  in
  BishopP.≤-respˡ-≃
    (factorShiftedResidualEquivalentToResidualShift rate pair)
    (Rate.shiftedResidualBelowTarget nPositive r≤n)

partitionErdosBishopFactorPairCubicResidualLevel : ProofLevel
partitionErdosBishopFactorPairCubicResidualLevel = machineChecked
