module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorStepReciprocalSquareExact where

------------------------------------------------------------------------
-- ERDOS FACTOR-STEP RECIPROCAL-SQUARE NORMALIZATION
--
-- For a classical factor pair r=k*v, the cubic translation step is
--
--   factorStep = k * x_n
--
-- where repeated Nat scaling is identified with multiplication by the embedded
-- positive Nat k.  Hence
--
--   factorStep^(-2) ≃ (k*)^(-2) * x_n^(-2).
--
-- This is the exact algebraic seam between the inner v*q^v kernel and the
-- outer Basel reciprocal-square sum.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopPositiveProductReciprocalSquareExact as ProductReciprocal
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
open import DASHI.Physics.YangMills.CompactLieProofLevel

copiesReal : ∀ {r} → Factor.PositiveFactorPair r → BishopReal.ℝ
copiesReal pair = Iterated.natReal (FactorResidual.factorCopies pair)

copiesRealPositive :
  ∀ {r} (pair : Factor.PositiveFactorPair r) →
  BishopReal._<_ BishopReal.0ℝ (copiesReal pair)
copiesRealPositive pair =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ
    (NatEmbed.natAsRational (FactorResidual.factorCopies pair))
    (ℚP.positive⁻¹
      (NatEmbed.natAsRational (FactorResidual.factorCopies pair)))

factorStepAsProduct :
  ∀ {n r} {nPositive : suc 0 Data.Nat.Base.≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  BishopReal._≃_
    (FactorResidual.factorStep rate pair)
    (BishopReal._*_
      (copiesReal pair)
      (Rate.step rate))
factorStepAsProduct rate pair =
  Iterated.natScaleAsEmbeddedNatMul
    (FactorResidual.factorCopies pair)
    (Rate.step rate)

factorStepInverseSquareAsProductInverseSquare :
  ∀ {n r} {nPositive : suc 0 Data.Nat.Base.≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  let
    factorPositive = FactorResidual.factorStepPositive rate pair
    copyPositive = copiesRealPositive pair
    stepPositive = Rate.stepPositive rate
    productPositive = ProductReciprocal.productPositive copyPositive stepPositive
  in
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (FactorResidual.factorStep rate pair)
      (Reciprocal.xNonzero factorPositive))
    (Reciprocal.inverseSquare
      (BishopReal._*_ (copiesReal pair) (Rate.step rate))
      (Reciprocal.xNonzero productPositive))
factorStepInverseSquareAsProductInverseSquare rate pair =
  let
    factorPositive = FactorResidual.factorStepPositive rate pair
    copyPositive = copiesRealPositive pair
    stepPositive = Rate.stepPositive rate
    productPositive = ProductReciprocal.productPositive copyPositive stepPositive
    inverseAgreement =
      BishopInverse.⁻¹-cong
        (Reciprocal.xNonzero factorPositive)
        (Reciprocal.xNonzero productPositive)
        (factorStepAsProduct rate pair)
  in
  BishopP.*-cong inverseAgreement inverseAgreement

factorStepReciprocalSquareNormalization :
  ∀ {n r} {nPositive : suc 0 Data.Nat.Base.≤ n}
    (rate : Rate.ErdosStepRate n nPositive)
    (pair : Factor.PositiveFactorPair r) →
  let
    factorPositive = FactorResidual.factorStepPositive rate pair
    copyPositive = copiesRealPositive pair
    stepPositive = Rate.stepPositive rate
  in
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (FactorResidual.factorStep rate pair)
      (Reciprocal.xNonzero factorPositive))
    (BishopReal._*_
      (Reciprocal.inverseSquare
        (copiesReal pair)
        (Reciprocal.xNonzero copyPositive))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero stepPositive)))
factorStepReciprocalSquareNormalization rate pair =
  let
    copyPositive = copiesRealPositive pair
    stepPositive = Rate.stepPositive rate
  in
  BishopP.≃-trans
    (factorStepInverseSquareAsProductInverseSquare rate pair)
    (ProductReciprocal.inverseSquareProduct copyPositive stepPositive)

partitionErdosBishopFactorStepReciprocalSquareLevel : ProofLevel
partitionErdosBishopFactorStepReciprocalSquareLevel = machineChecked
