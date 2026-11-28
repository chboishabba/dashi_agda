module DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationExact where

-- SOURCE-WRITTEN, kernel pending. Construct the descending column
-- for any integer Y from the SAME full candidate matrix. Reuse the
-- arbitrary specialization residual; its prefix and rigidity remain
-- explicit proof obligations, not consequences of this finite readout.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_∸_)
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Integer.Base as Z using (ℤ)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product.Base using (_,_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact as M
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Mat
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41SectorFilterExact as Filter
import DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceResidualExact as Residual
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as Root
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open Comp using (complexTrans; complexSym)
open N using (sumC; sumCong; sumMul)
open Poly using (realC)

columnCoefficient : Mat.Coefficient → ℤ → Fin 43 → ℤ
columnCoefficient c y i = Mat.zsum
  (λ j → Z._*_ (c (Mat.expo i) (Mat.expo j)) (M.zpow y (Mat.expo j)))

columnList : ∀ {n} → (Fin n → ℤ) → List ℚᵘ
columnList {zero} f = []
columnList {suc n} f = (f Fin.zero / 1) ∷ columnList (λ i → f (Fin.suc i))

lengthList : ∀ {n} (f : Fin n → ℤ) → length (columnList f) ≡ n
lengthList {zero} f = refl
lengthList {suc n} f = cong suc (lengthList (λ i → f (Fin.suc i)))

column : Mat.Coefficient → ℤ → List ℚᵘ
column c y = columnList (columnCoefficient c y)

degreeColumn : ∀ c y → Poly.degree (column c y) ≡ 42
degreeColumn c y = lengthList (λ i → columnCoefficient c y (Fin.suc i))

polyList : ∀ {n} x (f : Fin n → ℤ) →
  Poly.poly x (columnList f) ≈C
    sumC (λ i → realC (I.embed (f i)) *C powC x (n ∸ suc (toℕ i)))
polyList {zero} x f = C.≈C-refl _
polyList {suc n} x f = A.addCCongruent
  (A.mulCCongruent (C.≈C-refl _)
    (Filter.powIndex x (lengthList (λ i → f (Fin.suc i)))))
  (polyList x (λ i → f (Fin.suc i)))

innerRead : ∀ c x y i →
  sumC (Mat.term c x (realC (I.embed y)) i) ≈C
    (realC (I.embed (columnCoefficient c y i)) *C powC x (Mat.expo i))
innerRead c x y i =
  complexTrans (sumMul (λ j → realC (I.embed (c (Mat.expo i) (Mat.expo j))) *C
    powC (realC (I.embed y)) (Mat.expo j)) (powC x (Mat.expo i)))
    (A.mulCCongruent
      (complexTrans (sumCong _ _ (λ j →
        complexTrans (A.mulCCongruent (C.≈C-refl _) (Mat.zpowRead y (Mat.expo j)))
          (complexTrans (Root.realMul _ _) (P.≃-symm (I.embedMul _ _) , P.≃-refl))))
        (Mat.zsumRead _)) (C.≈C-refl _))

matrixRead : ∀ c x y → Mat.matrix c x (realC (I.embed y)) ≈C Poly.poly x (column c y)
matrixRead c x y = complexTrans (sumCong _ _ (innerRead c x y))
  (complexSym (polyList x (columnCoefficient c y)))

module At (inputs : Round11.BishopCutset) where
  module R = Residual.At inputs

  module For (c : Mat.Coefficient) (y : ℤ) where
    module S = R.For (I.embed y) (column c y) (degreeColumn c y)

    actualIdentity : ∀ p → S.residual p ≈C A.zeroC →
      R.G.product p (realC (I.embed y)) ≈C Mat.matrix c (R.G.j p) (realC (I.embed y))
    actualIdentity p zeroResidual = complexTrans (Cross.zeroDifference _ _ zeroResidual)
      (complexSym (matrixRead c (R.G.j p) y))
