module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairInverseSquareNormalizationExact where

------------------------------------------------------------------------
-- FACTOR-STEP RECIPROCAL-SQUARE NORMALIZATION
--
-- The factor-pair cubic kernel produces
--
--   inverseSquare (factorStep rate pair),
--
-- where factorStep is k repeated copies of the shared x_n step.  Normalize it
-- exactly into the Basel-facing product
--
--   inverseSquare (natReal k) * inverseSquare x_n.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopInverseSquareProductExact as ProductInverse
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorCopiesNatRealPositive :
  ∀ {r : Nat} (pair : Factor.PositiveFactorPair r) →
  BishopReal._<_ BishopReal.0ℝ
    (Iterated.natReal (FactorResidual.factorCopies pair))
factorCopiesNatRealPositive pair =
  NatPositive.natRealSuccessorStrictlyPositive (Factor.predecessor pair)

factorStepProductPositive :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._*_
      (Iterated.natReal (FactorResidual.factorCopies pair))
      (Rate.step rate))
factorStepProductPositive rate pair =
  ProductInverse.productPositive
    (factorCopiesNatRealPositive pair)
    (Rate.stepPositive rate)

factorStepAsNatProduct :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (FactorResidual.factorStep rate pair)
    (BishopReal._*_
      (Iterated.natReal (FactorResidual.factorCopies pair))
      (Rate.step rate))
factorStepAsNatProduct rate pair =
  Iterated.natScaleAsEmbeddedNatMul
    (FactorResidual.factorCopies pair)
    (Rate.step rate)

factorStepInverseSquareAsNatProduct :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (FactorResidual.factorStep rate pair)
      (Reciprocal.xNonzero (FactorResidual.factorStepPositive rate pair)))
    (Reciprocal.inverseSquare
      (BishopReal._*_
        (Iterated.natReal (FactorResidual.factorCopies pair))
        (Rate.step rate))
      (ProductInverse.productNonzero
        (factorCopiesNatRealPositive pair)
        (Rate.stepPositive rate)))
factorStepInverseSquareAsNatProduct rate pair =
  ProductInverse.inverseSquareCongruentPositive
    (FactorResidual.factorStepPositive rate pair)
    (factorStepProductPositive rate pair)
    (factorStepAsNatProduct rate pair)

factorStepInverseSquareNormalization :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (FactorResidual.factorStep rate pair)
      (Reciprocal.xNonzero (FactorResidual.factorStepPositive rate pair)))
    (BishopReal._*_
      (Reciprocal.inverseSquare
        (Iterated.natReal (FactorResidual.factorCopies pair))
        (Reciprocal.xNonzero (factorCopiesNatRealPositive pair)))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
factorStepInverseSquareNormalization rate pair =
  BishopP.≃-trans
    (factorStepInverseSquareAsNatProduct rate pair)
    (ProductInverse.inverseSquareProduct
      (factorCopiesNatRealPositive pair)
      (Rate.stepPositive rate))

canonicalFactorStepInverseSquareNormalization :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  (pair : Factor.PositiveFactorPair r) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (FactorResidual.factorStep rate pair)
      (Reciprocal.xNonzero (FactorResidual.factorStepPositive rate pair)))
    (BishopReal._*_
      (Reciprocal.inverseSquare
        (Iterated.natReal (FactorResidual.factorCopies pair))
        (Reciprocal.xNonzero (factorCopiesNatRealPositive pair)))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
canonicalFactorStepInverseSquareNormalization {n} nPositive pair =
  factorStepInverseSquareNormalization
    (Rate.canonicalErdosStepRate n nPositive)
    pair

partitionErdosBishopFactorPairInverseSquareNormalizationLevel : ProofLevel
partitionErdosBishopFactorPairInverseSquareNormalizationLevel = machineChecked
