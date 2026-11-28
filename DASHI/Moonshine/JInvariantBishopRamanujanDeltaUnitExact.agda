module DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact where

-- SOURCE-WRITTEN, kernel pending. The already-existing literal Ramanujan
-- coefficients yield the discriminant flow and normalized cusp unit.
-- This is a formal all-index proof, not an analytic nonvanishing claim.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as Z using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as T
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as Flow
import DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact as Inv
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as Ram
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as Unique
open G
open U using (X; Y; X2; X3; Y2; disc)
open T using (E)
open F using (δ; dCong; dMul; dSub; dScale; scaleCong)
open H using (zeroSeries; unitSeries)

xFlow : δ X3 ≈s ((E ⊗s X3) ⊖s (X2 ⊗s Y))
xFlow = transS (dMul X2 X)
  (transS (addCong
    (mulCong (transS (dMul X X)
      (addCong (mulCong Ram.ramanujanX reflS) (mulCong reflS Ram.ramanujanX))) reflS)
    (mulCong reflS Ram.ramanujanX))
    (transS (addCong (mulCong (addCong
      (mulCong (scaleIsProduct (+ 1 / 3) _) reflS)
      (mulCong reflS (scaleIsProduct (+ 1 / 3) _))) reflS)
      (mulCong reflS (scaleIsProduct (+ 1 / 3) _)))
      (let open G.Solver in
       solve 3 (λ e x y →
         ((((Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)) ⊗ x) ⊕
           (x ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)))) ⊗ x) ⊕
           ((x ⊗ x) ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)))
           ⊜ e ⊗ ((x ⊗ x) ⊗ x) ⊖ ((x ⊗ x) ⊗ y)) reflS E X Y)))

yFlow : δ Y2 ≈s ((E ⊗s Y2) ⊖s (X2 ⊗s Y))
yFlow = transS (dMul Y Y)
  (transS (addCong (mulCong Ram.ramanujanY reflS) (mulCong reflS Ram.ramanujanY))
    (transS (addCong (mulCong (scaleIsProduct (+ 1 / 2) _) reflS)
      (mulCong reflS (scaleIsProduct (+ 1 / 2) _)))
      (let open G.Solver in
       solve 3 (λ e x y →
         (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x)) ⊗ y ⊕
           y ⊗ (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x))
           ⊜ e ⊗ (y ⊗ y) ⊖ ((x ⊗ x) ⊗ y)) reflS E X Y)))

discFlow : δ disc ≈s (E ⊗s disc)
discFlow = transS (dSub X3 Y2)
  (transS (subCong xFlow yFlow)
    (let open G.Solver in solve 4
      (λ e a b c → (e ⊗ a ⊖ c) ⊖ (e ⊗ b ⊖ c) ⊜ e ⊗ (a ⊖ b))
      reflS E X3 Y2 (X2 ⊗s Y)))

Delta : Series
Delta = scale ((+ 1 / 1728) R.⋆) disc

deltaFlow : δ Delta ≈s (E ⊗s Delta)
deltaFlow = transS (dScale (+ 1 / 1728) disc)
  (transS (scaleCong (+ 1 / 1728) discFlow)
    (transS (scaleIsProduct (+ 1 / 1728) (E ⊗s disc))
      (transS (let open G.Solver in solve 2
        (λ e d → Κ (+ 1 / 1728) ⊗ (e ⊗ d) ⊜ e ⊗ (Κ (+ 1 / 1728) ⊗ d))
        reflS E disc)
        (mulCong reflS (symS (scaleIsProduct (+ 1 / 1728) disc))))))

delta0 : R._≃_ (Delta zero) R.0ℝ
delta0 = U.right0 U.disc0

-- The first normalized coefficient is 1 by the actual first E4/E6
-- terms, not by imposing a new normalization premise.
x1 : R._≃_ (X 1) ((+ 240 / 1) R.⋆)
x1 = P.≃-refl
y1 : R._≃_ (Y 1) ((Z.- (+ 504) / 1) R.⋆)
y1 = P.≃-symm (P.⋆-distrib-neg (+ 504 / 1))

firstRow : ∀ f g → R._≃_ ((f ⊗s g) 1)
  (R._+_ (R._*_ (f zero) (g 1)) (R._*_ (f 1) (g zero)))
firstRow f g = P.≃-trans (Row.cauchyCoefficientSuccessor f g zero)
  (P.+-cong P.≃-refl (Row.cauchyCoefficientZero (Row.shift f) g))

x21 : R._≃_ (X2 1) ((+ 480 / 1) R.⋆)
x21 = P.≃-trans (firstRow X X)
  (P.≃-trans (P.+-cong (P.*-congˡ x1) (P.*-congʳ x1))
    (let open P.ℝ-Solver in solve 0
      (Κ 1ℚᵘ ⊗ Κ (+ 240 / 1) ⊕ Κ (+ 240 / 1) ⊗ Κ 1ℚᵘ ⊜ Κ (+ 480 / 1)) P.≃-refl))

x31 : R._≃_ (X3 1) ((+ 720 / 1) R.⋆)
x31 = P.≃-trans (firstRow X2 X)
  (P.≃-trans (P.+-cong (P.*-cong U.x20 x1) (P.*-congʳ x21))
    (let open P.ℝ-Solver in solve 0
      (Κ 1ℚᵘ ⊗ Κ (+ 240 / 1) ⊕ Κ (+ 480 / 1) ⊗ Κ 1ℚᵘ ⊜ Κ (+ 720 / 1)) P.≃-refl))

y21 : R._≃_ (Y2 1) ((Z.- (+ 1008) / 1) R.⋆)
y21 = P.≃-trans (firstRow Y Y)
  (P.≃-trans (P.+-cong (P.*-congˡ y1) (P.*-congʳ y1))
    (let open P.ℝ-Solver in solve 0
      (Κ 1ℚᵘ ⊗ (⊝ Κ (+ 504 / 1)) ⊕ (⊝ Κ (+ 504 / 1)) ⊗ Κ 1ℚᵘ
       ⊜ ⊝ Κ (+ 1008 / 1)) P.≃-refl))

delta1 : R._≃_ (Delta 1) R.1ℝ
delta1 = P.≃-trans (P.*-congˡ (P.+-cong x31 (P.-‿cong y21)))
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1 / 1728) ⊗ (Κ (+ 720 / 1) ⊖ (⊝ Κ (+ 1008 / 1))) ⊜ Κ 1ℚᵘ) P.≃-refl)

-- Shift at the actual zero mode. No formal division by q.
unit : Series
unit = Row.shift Delta

unit0 : R._≃_ (unit zero) R.1ℝ
unit0 = delta1

shiftRight : ∀ a b → R._≃_ (b zero) R.0ℝ →
  Row.shift (a ⊗s b) ≈s (a ⊗s Row.shift b)
shiftRight a b hb n = P.≃-trans (Ring.rowComm a b (suc n))
  (P.≃-trans (U.zeroHead b a hb n) (Ring.rowComm (Row.shift b) a n))

shiftEuler : ∀ f → Row.shift (δ f) ≈s (δ (Row.shift f) ⊕s Row.shift f)
shiftEuler f n =
  P.≃-trans (P.*-congʳ (P.*-congˡ (NR.natRealAdd n 1)))
    (let open P.ℝ-Solver in solve 2
      (λ n x → (Κ 1ℚᵘ ⊗ (n ⊕ Κ 1ℚᵘ)) ⊗ x ⊜ (Κ 1ℚᵘ ⊗ n) ⊗ x ⊕ x)
      P.≃-refl (NR.natReal n) (f (suc n)))

Eplus : Series
Eplus = E ⊖s unitSeries

Eplus0 : R._≃_ (Eplus zero) R.0ℝ
Eplus0 = P.+-inverseʳ R.1ℝ

unitFlow : δ unit ≈s (Eplus ⊗s unit)
unitFlow =
  transS (let open G.Solver in solve 2 (λ d u → d ⊜ (d ⊕ u) ⊖ u) reflS (δ unit) unit)
    (transS (subCong (transS (symS (shiftEuler Delta))
      (transS (λ n → deltaFlow (suc n)) (shiftRight E Delta delta0))) reflS)
      (transS (subCong reflS (symS (Ring.rowUnitLeft unit)))
        (let open G.Solver in solve 3
          (λ e u one → e ⊗ u ⊖ one ⊗ u ⊜ (e ⊖ one) ⊗ u)
          reflS E unit unitSeries)))

-- A literal reciprocal unit from the existing zero-mode formal inverse.
-- This proves invertibility in the formal ring, not yet at every q.
inverseInner : Series
inverseInner = unitSeries ⊖s unit

inner0 : R._≃_ (inverseInner zero) R.0ℝ
inner0 = P.≃-trans (P.+-cong P.≃-refl (P.-‿cong unit0)) (P.+-inverseʳ R.1ℝ)

reciprocal : Series
reciprocal = Inv.geometric inverseInner

unitInverse : (unit ⊗s reciprocal) ≈s unitSeries
unitInverse = transS (mulCong (let open G.Solver in solve 2
  (λ o u → u ⊜ o ⊖ (o ⊖ u)) reflS unitSeries unit) reflS)
  (Inv.inverseFromZeroMode inverseInner inner0)

reciprocal0 : R._≃_ (reciprocal zero) R.1ℝ
reciprocal0 = H.composeZero (λ _ → R.1ℝ) inverseInner

inverseFlow : δ reciprocal ≈s neg (Eplus ⊗s reciprocal)
inverseFlow =
  let prodZero = transS (symS (dMul unit reciprocal))
        (transS (dCong unitInverse) Flow.dUnit)
      sumZero = transS (addCong (mulCong (symS unitFlow) reflS) reflS) prodZero
      factorZero = transS (let open G.Solver in solve 4
        (λ u e v d → u ⊗ (d ⊕ e ⊗ v) ⊜ (e ⊗ u) ⊗ v ⊕ u ⊗ d)
        reflS unit Eplus reciprocal (δ reciprocal)) sumZero
      a = δ reciprocal ⊕s (Eplus ⊗s reciprocal)
      az = transS (symS (Ring.rowUnitLeft a))
        (transS (mulCong (symS unitInverse) reflS)
          (transS (let open G.Solver in solve 3
            (λ u v a → (u ⊗ v) ⊗ a ⊜ v ⊗ (u ⊗ a)) reflS unit reciprocal a)
            (transS (mulCong reflS factorZero) (let open G.Solver in solve 1
              (λ x → x ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) reflS reciprocal))))
  in transS (let open G.Solver in solve 2
       (λ d e → d ⊜ (d ⊕ e) ⊖ e) reflS (δ reciprocal) (Eplus ⊗s reciprocal))
       (transS (subCong az reflS) (let open G.Solver in solve 1
         (λ e → Κ 0ℚᵘ ⊖ e ⊜ ⊝ e) reflS (Eplus ⊗s reciprocal)))
