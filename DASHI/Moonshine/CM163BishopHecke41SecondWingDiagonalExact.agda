module DASHI.Moonshine.CM163BishopHecke41SecondWingDiagonalExact where

-- SOURCE-WRITTEN, kernel pending. Read the actual second wing at
-- coincident endpoints. The triangular count is a real embedding of
-- 1+2+...+(n+1), i.e. choose(n+2,2), with no division at the center.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _+_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact as T
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)

count : Nat → ℝ
count zero = R.1ℝ
count (suc n) = NR.natReal (suc (suc n)) + count n

scaleAdd : ∀ h k z → (scaleC h z +C scaleC k z) ≈C scaleC (h + k) z
scaleAdd h k (C.complex x y) =
  P.≃-symm (P.*-distribʳ-+ x h k) ,
  P.≃-symm (P.*-distribʳ-+ y h k)

oneWing : ∀ u v → D.Q u v 1 ≈C A.oneC
oneWing u v =
  complexTrans (D.qStep u v zero)
    (complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero u))
      (L.complexAddRightIdentity _))

oneSecond : ∀ u v w → T.T u v w 1 ≈C A.zeroC
oneSecond u v w =
  complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero u))
    (L.complexAddRightIdentity _)

diagonal : ∀ u n → T.T u u u (suc (suc n)) ≈C scaleC (count n) (powC u n)
diagonal u zero =
  complexTrans (A.addCCongruent (oneWing u u)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (oneSecond u u u))
      (L.complexMultiplyRightZero u)))
    (complexTrans (L.complexAddRightIdentity _)
      (complexSym (Ram.scaleOne A.oneC)))
diagonal u (suc n) =
  complexTrans (A.addCCongruent (D.wingDiagonal u zero (suc n))
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (diagonal u n))
      (Fixed.scaleRight (count n) u (powC u n))))
    (scaleAdd (NR.natReal (suc (suc n))) (count n) (powC u (suc n)))

diagonalCoefficient : ∀ f u n → T.terms f u u u (suc (suc n)) ≈C
  scaleC (count n) (f (suc (suc n)) *C powC u n)
diagonalCoefficient f u n =
  complexTrans (A.mulCCongruent (C.≈C-refl _) (diagonal u n))
    (Fixed.scaleRight (count n) (f (suc (suc n))) (powC u n))
