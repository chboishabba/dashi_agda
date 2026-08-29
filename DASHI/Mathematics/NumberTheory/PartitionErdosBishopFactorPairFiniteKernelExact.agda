module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairFiniteKernelExact where

------------------------------------------------------------------------
-- FACTOR-PAIR FINITE DEGREE-ONE CUBIC KERNEL
--
-- For a classical factor pair r = k*v, the residual translation owner uses
-- the positive step k*x_n.  The generic cubic finite-kernel theorem therefore
-- applies directly at that same step:
--
--   W_N(q(k*x_n)) < (k*x_n)^(-2).
--
-- No residual reindexing, Basel input, or infinite-series argument enters this
-- owner.  It is the local analytic receipt attached to one classical factor
-- coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal

import DASHI.Foundations.BishopCubicTranslationFiniteDegreeOneKernelExact as Kernel
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Cross
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorPairFiniteDegreeOneKernel :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n} →
  (rate : Rate.ErdosStepRate n nPositive) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (Cross.inverseSquare step (Cross.xNonzero stepPositive))
factorPairFiniteDegreeOneKernel rate pair count =
  Kernel.cubicFiniteDegreeOneKernel
    (FactorResidual.factorStepPositive rate pair)
    count

canonicalFactorPairFiniteDegreeOneKernel :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (Cross.inverseSquare step (Cross.xNonzero stepPositive))
canonicalFactorPairFiniteDegreeOneKernel {n} nPositive pair count =
  factorPairFiniteDegreeOneKernel
    (Rate.canonicalErdosStepRate n nPositive)
    pair count

partitionErdosBishopFactorPairFiniteKernelLevel : ProofLevel
partitionErdosBishopFactorPairFiniteKernelLevel = machineChecked
