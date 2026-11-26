module DASHI.Moonshine.JInvariantBishopFormalZFlowExact where

-- SOURCE-WRITTEN, UNCOMPILED. Original coordinate Z=(X^3-Y^2)/X^3
-- obeys X DZ=Y Z using only literal Ramanujan identities and the
-- finite geometric inverse. No division by q or by Z.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as T
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact as I
open G
open U using (X; Y; X2; X3; Y2; disc)
open T using (E)
open H using (Zcoord; inverseX3; unitSeries; zeroSeries)
open F using (δ; dCong; dMul; dSub; RamanujanX; RamanujanY)

dX3 : δ X3 ≈s scale ((+ 3 / 1) ⋆) (X2 ⊗s δ X)
dX3 =
  transS (dMul X2 X)
    (transS (addCong (mulCong (dMul X X) reflS) reflS)
      (transS (let open G.Solver in
        solve 2 (λ x dx → ((dx ⊗ x ⊕ x ⊗ dx) ⊗ x) ⊕ ((x ⊗ x) ⊗ dx)
          ⊜ Κ (+ 3 / 1) ⊗ ((x ⊗ x) ⊗ dx)) reflS X (δ X))
        (symS (scaleIsProduct (+ 3 / 1) (X2 ⊗s δ X)))))

dX3Ramanujan : RamanujanX →
  δ X3 ≈s ((E ⊗s X3) ⊖s (X2 ⊗s Y))
dX3Ramanujan hx =
  transS dX3
    (transS (F.scaleCong (+ 3 / 1) (mulCong reflS hx))
      (transS (scaleIsProduct (+ 3 / 1) (X2 ⊗s scale ((+ 1 / 3) ⋆) ((E ⊗s X) ⊖s Y)))
        (transS (mulCong reflS (mulCong reflS (scaleIsProduct (+ 1 / 3) ((E ⊗s X) ⊖s Y))))
          (let open G.Solver in
            solve 3 (λ x y e → Κ (+ 3 / 1) ⊗ ((x ⊗ x) ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)))
              ⊜ e ⊗ ((x ⊗ x) ⊗ x) ⊖ (x ⊗ x) ⊗ y) reflS X Y E))))

dY2Ramanujan : RamanujanY →
  δ Y2 ≈s ((E ⊗s Y2) ⊖s (X2 ⊗s Y))
dY2Ramanujan hy =
  transS (dMul Y Y)
    (transS (addCong (mulCong hy reflS) (mulCong reflS hy))
      (transS (addCong (mulCong (scaleIsProduct (+ 1 / 2) ((E ⊗s Y) ⊖s X2)) reflS)
        (mulCong reflS (scaleIsProduct (+ 1 / 2) ((E ⊗s Y) ⊖s X2))))
        (let open G.Solver in
          solve 3 (λ x y e → (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x)) ⊗ y ⊕
            y ⊗ (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x))
            ⊜ e ⊗ (y ⊗ y) ⊖ (x ⊗ x) ⊗ y) reflS X Y E)))

dDisc : RamanujanX → RamanujanY → δ disc ≈s (E ⊗s disc)
dDisc hx hy =
  transS (dSub X3 Y2)
    (transS (subCong (dX3Ramanujan hx) (dY2Ramanujan hy))
      (let open G.Solver in
        solve 4 (λ e x3 y2 t → (e ⊗ x3 ⊖ t) ⊖ (e ⊗ y2 ⊖ t)
          ⊜ e ⊗ (x3 ⊖ y2)) reflS E X3 Y2 (X2 ⊗s Y)))

ZResidual : Series
ZResidual = (X ⊗s δ Zcoord) ⊖s (Y ⊗s Zcoord)

scaledZResidual : RamanujanX →
  (X2 ⊗s ZResidual) ≈s
  (δ (X3 ⊗s Zcoord) ⊖s (E ⊗s (X3 ⊗s Zcoord)))
scaledZResidual hx =
  symS (transS (subCong (dMul X3 Zcoord) reflS)
    (transS (subCong (addCong (mulCong (dX3Ramanujan hx) reflS) reflS) reflS)
      (let open G.Solver in
        solve 5 (λ x y e z dz →
          ((e ⊗ ((x ⊗ x) ⊗ x) ⊖ (x ⊗ x) ⊗ y) ⊗ z ⊕
             ((x ⊗ x) ⊗ x) ⊗ dz) ⊖ e ⊗ (((x ⊗ x) ⊗ x) ⊗ z)
          ⊜ (x ⊗ x) ⊗ (x ⊗ dz ⊖ y ⊗ z))
          reflS X Y E Zcoord (δ Zcoord))))

scaledZZero : RamanujanX → RamanujanY → (X2 ⊗s ZResidual) ≈s zeroSeries
scaledZZero hx hy =
  transS (scaledZResidual hx)
    (transS (subCong (dCong I.actualZDenominator) (mulCong reflS I.actualZDenominator))
      (transS (subCong (dDisc hx hy) reflS)
        (let open G.Solver in solve 1 (λ a → a ⊖ a ⊜ Κ 0ℚᵘ) reflS (E ⊗s disc))))

x2Inverse : ((X ⊗s inverseX3) ⊗s X2) ≈s unitSeries
x2Inverse =
  transS (let open G.Solver in
    solve 2 (λ x i → (x ⊗ i) ⊗ (x ⊗ x) ⊜ ((x ⊗ x) ⊗ x) ⊗ i)
      reflS X inverseX3) I.actualInverseX3

zResidualZero : RamanujanX → RamanujanY → ZResidual ≈s zeroSeries
zResidualZero hx hy =
  transS (symS (W.rowUnitLeft ZResidual))
    (transS (mulCong (symS x2Inverse) reflS)
      (transS (W.rowAssoc (X ⊗s inverseX3) X2 ZResidual)
        (transS (mulCong reflS (scaledZZero hx hy))
          (H.zeroRow (X ⊗s inverseX3)))))

actualZFlow : RamanujanX → RamanujanY →
  (X ⊗s δ Zcoord) ≈s (Y ⊗s Zcoord)
actualZFlow hx hy n =
  let a = (X ⊗s δ Zcoord) n
      b = (Y ⊗s Zcoord) n
      open P.ℝ-Solver
  in P.≃-trans (solve 2 (λ a b → a ⊜ (a ⊖ b) ⊕ b) P.≃-refl a b)
    (P.≃-trans (P.+-cong (zResidualZero hx hy n) P.≃-refl)
      (P.+-identityˡ b))
