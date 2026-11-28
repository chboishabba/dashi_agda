module DASHI.Moonshine.JInvariantBishopFormalHyperClearedODEExact where

-- SOURCE-WRITTEN, UNCOMPILED. Denominator jet assembly on original
-- coefficient streams. No division by Y or by q. The rational solver
-- sees only the existing Cauchy ring, with literal congruence transports.
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Int
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as T
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as CF
import DASHI.Moonshine.JInvariantBishopFormalHyperRecurrenceExact as HR
open G
open U using (X; Y; A; B)
open F using (δ; dCong; dAdd; dSub; dMul; RamanujanX; RamanujanY; RamanujanE)
open CF using (C; actualChain; composeOuterCong)

f f1 f2 f3 : Series
f = C zero
f1 = δ f
f2 = δ f1
f3 = δ f2

cancelShared : (t a b : Series) → (t ⊕s a) ≈s (t ⊕s b) → a ≈s b
cancelShared t a b h =
  transS (let open G.Solver in solve 2 (λ t a → a ⊜ (t ⊕ a) ⊖ t) reflS t a)
    (transS (subCong h reflS)
      (let open G.Solver in solve 2 (λ t b → (t ⊕ b) ⊖ t ⊜ b) reflS t b))

chain0 : RamanujanX → RamanujanY → (Y ⊗s C 1) ≈s (X ⊗s f1)
chain0 hx hy = symS (actualChain hx hy zero)

left2 : RamanujanX → RamanujanY → ((X ⊗s Y) ⊗s (δ (Y ⊗s (C 1)))) ≈s ((((X ⊗s X) ⊗s (δ Y)) ⊗s f1) ⊕s (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)))
left2 hx hy =
  (transS (mulCong reflS (transS (dMul Y (C 1)) (addCong (mulCong reflS reflS) (mulCong reflS reflS)))) (transS (transS (mulCong (mulCong reflS reflS) (addCong (mulCong reflS reflS) (mulCong reflS reflS))) (transS (let open G.Solver in solve 5 (λ x y dy c1 dc1 → ((x ⊗ y) ⊗ ((dy ⊗ c1) ⊕ (y ⊗ dc1))) ⊜ (((x ⊗ dy) ⊗ (y ⊗ c1)) ⊕ ((y ⊗ y) ⊗ (x ⊗ dc1)))) reflS X Y (δ Y) (C 1) (δ (C 1))) (symS (addCong (mulCong (mulCong reflS reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) (mulCong reflS reflS)))))) (transS (addCong (mulCong reflS (chain0 hx hy)) (mulCong reflS (actualChain hx hy 1))) (transS (addCong (mulCong (mulCong reflS reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) (mulCong reflS reflS))) (transS (let open G.Solver in solve 5 (λ x dy u y c2 → (((x ⊗ dy) ⊗ (x ⊗ u)) ⊕ ((y ⊗ y) ⊗ (y ⊗ c2))) ⊜ ((((x ⊗ x) ⊗ dy) ⊗ u) ⊕ (((y ⊗ y) ⊗ y) ⊗ c2))) reflS X (δ Y) f1 Y (C 2)) (symS (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong (mulCong reflS reflS) reflS) reflS))))))))

right2 : ((X ⊗s Y) ⊗s (δ (X ⊗s f1))) ≈s ((((X ⊗s X) ⊗s (δ Y)) ⊗s f1) ⊕s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))
right2 =
  (transS (mulCong reflS (transS (dMul X f1) (addCong (mulCong reflS reflS) (mulCong reflS reflS)))) (transS (mulCong (mulCong reflS reflS) (addCong (mulCong reflS reflS) (mulCong reflS reflS))) (transS (let open G.Solver in solve 6 (λ x y dx u v dy → ((x ⊗ y) ⊗ ((dx ⊗ u) ⊕ (x ⊗ v))) ⊜ ((((x ⊗ x) ⊗ dy) ⊗ u) ⊕ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊗ u)))) reflS X Y (δ X) f1 f2 (δ Y)) (symS (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS (subCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS)))))))

secondJet : RamanujanX → RamanujanY → (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)) ≈s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1))
secondJet hx hy =
  cancelShared (((X ⊗s X) ⊗s (δ Y)) ⊗s f1) (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)) ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)) (transS (symS (left2 hx hy)) (transS (mulCong reflS (dCong (chain0 hx hy))) right2))

left3 : RamanujanX → RamanujanY → ((X ⊗s Y) ⊗s (δ (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)))) ≈s ((scale (((+ 3) / 1) ⋆) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ⊕s ((((Y ⊗s Y) ⊗s Y) ⊗s (Y ⊗s Y)) ⊗s (C 3)))
left3 hx hy =
  (transS (mulCong reflS (transS (dMul ((Y ⊗s Y) ⊗s Y) (C 2)) (addCong (mulCong (transS (dMul (Y ⊗s Y) Y) (addCong (mulCong (transS (dMul Y Y) (addCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS) (mulCong reflS reflS))) reflS) (mulCong reflS reflS)))) (transS (transS (mulCong (mulCong reflS reflS) (addCong (mulCong (addCong (mulCong (addCong (mulCong reflS reflS) (mulCong reflS reflS)) reflS) (mulCong (mulCong reflS reflS) reflS)) reflS) (mulCong (mulCong (mulCong reflS reflS) reflS) reflS))) (transS (let open G.Solver in solve 5 (λ x y dy c2 dc2 → ((x ⊗ y) ⊗ ((((((dy ⊗ y) ⊕ (y ⊗ dy)) ⊗ y) ⊕ ((y ⊗ y) ⊗ dy)) ⊗ c2) ⊕ (((y ⊗ y) ⊗ y) ⊗ dc2))) ⊜ ((Κ ((+ 3) / 1) ⊗ ((x ⊗ dy) ⊗ (((y ⊗ y) ⊗ y) ⊗ c2))) ⊕ ((((y ⊗ y) ⊗ y) ⊗ y) ⊗ (x ⊗ dc2)))) reflS X Y (δ Y) (C 2) (δ (C 2))) (symS (addCong (transS (scaleIsProduct ((+ 3) / 1) ((X ⊗s (δ Y)) ⊗s (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)))) (mulCong reflS (mulCong (mulCong reflS reflS) (mulCong (mulCong (mulCong reflS reflS) reflS) reflS)))) (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong reflS reflS)))))) (transS (addCong (F.scaleCong (+ 3 / 1) (mulCong reflS (secondJet hx hy))) (mulCong reflS (actualChain hx hy 2))) (transS (addCong (transS (scaleIsProduct ((+ 3) / 1) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) (mulCong reflS (mulCong (mulCong reflS reflS) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))) (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong reflS reflS))) (transS (let open G.Solver in solve 7 (λ x dy y v a u c3 → ((Κ ((+ 3) / 1) ⊗ ((x ⊗ dy) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ a) ⊗ u)))) ⊕ ((((y ⊗ y) ⊗ y) ⊗ y) ⊗ (y ⊗ c3))) ⊜ ((Κ ((+ 3) / 1) ⊗ ((x ⊗ dy) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ a) ⊗ u)))) ⊕ ((((y ⊗ y) ⊗ y) ⊗ (y ⊗ y)) ⊗ c3))) reflS X (δ Y) Y f2 A f1 (C 3)) (symS (addCong (transS (scaleIsProduct ((+ 3) / 1) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) (mulCong reflS (mulCong (mulCong reflS reflS) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))) (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS))))))))

right3 : ((X ⊗s Y) ⊗s (δ ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ≈s ((scale (((+ 3) / 1) ⋆) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ⊕s ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1)))
right3 =
  (transS (mulCong reflS (transS (dAdd (((X ⊗s X) ⊗s Y) ⊗s f2) ((X ⊗s A) ⊗s f1)) (addCong (transS (dMul ((X ⊗s X) ⊗s Y) f2) (addCong (mulCong (transS (dMul (X ⊗s X) Y) (addCong (mulCong (transS (dMul X X) (addCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS) (mulCong reflS reflS))) reflS) (mulCong reflS reflS))) (transS (dMul (X ⊗s A) f1) (addCong (mulCong (transS (dMul X A) (addCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS) (mulCong reflS reflS)))))) (transS (mulCong (mulCong reflS reflS) (addCong (addCong (mulCong (addCong (mulCong (addCong (mulCong reflS reflS) (mulCong reflS reflS)) reflS) (mulCong (mulCong reflS reflS) reflS)) reflS) (mulCong (mulCong (mulCong reflS reflS) reflS) reflS)) (addCong (mulCong (addCong (mulCong reflS (subCong (mulCong reflS reflS) (mulCong reflS reflS))) (mulCong reflS reflS)) reflS) (mulCong (mulCong reflS (subCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS)))) (transS (let open G.Solver in solve 8 (λ x y dx dy v w da u → ((x ⊗ y) ⊗ (((((((dx ⊗ x) ⊕ (x ⊗ dx)) ⊗ y) ⊕ ((x ⊗ x) ⊗ dy)) ⊗ v) ⊕ (((x ⊗ x) ⊗ y) ⊗ w)) ⊕ ((((dx ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊕ (x ⊗ da)) ⊗ u) ⊕ ((x ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊗ v)))) ⊜ ((Κ ((+ 3) / 1) ⊗ ((x ⊗ dy) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊗ u)))) ⊕ ((((((x ⊗ x) ⊗ x) ⊗ (y ⊗ y)) ⊗ w) ⊕ (Κ ((+ 3) / 1) ⊗ ((((x ⊗ x) ⊗ y) ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊗ v))) ⊕ ((x ⊗ ((((y ⊗ dx) ⊖ (x ⊗ dy)) ⊗ ((y ⊗ dx) ⊖ (x ⊗ dy))) ⊕ (x ⊗ ((y ⊗ da) ⊖ (Κ ((+ 2) / 1) ⊗ (((y ⊗ dx) ⊖ (x ⊗ dy)) ⊗ dy)))))) ⊗ u)))) reflS X Y (δ X) (δ Y) f2 f3 (δ A) f1) (symS (addCong (transS (scaleIsProduct ((+ 3) / 1) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s ((Y ⊗s (δ X)) ⊖s (X ⊗s (δ Y)))) ⊗s f1)))) (mulCong reflS (mulCong (mulCong reflS reflS) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS (subCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS))))) (addCong (addCong (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS) (transS (scaleIsProduct ((+ 3) / 1) ((((X ⊗s X) ⊗s Y) ⊗s ((Y ⊗s (δ X)) ⊖s (X ⊗s (δ Y)))) ⊗s f2)) (mulCong reflS (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) (subCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS)))) (mulCong (mulCong reflS (addCong (mulCong (subCong (mulCong reflS reflS) (mulCong reflS reflS)) (subCong (mulCong reflS reflS) (mulCong reflS reflS))) (mulCong reflS (subCong (mulCong reflS reflS) (transS (scaleIsProduct ((+ 2) / 1) (((Y ⊗s (δ X)) ⊖s (X ⊗s (δ Y))) ⊗s (δ Y))) (mulCong reflS (mulCong (subCong (mulCong reflS reflS) (mulCong reflS reflS)) reflS))))))) reflS)))))))

thirdJet : RamanujanX → RamanujanY → ((((Y ⊗s Y) ⊗s Y) ⊗s (Y ⊗s Y)) ⊗s (C 3)) ≈s ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1))
thirdJet hx hy =
  cancelShared (scale (((+ 3) / 1) ⋆) ((X ⊗s (δ Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ((((Y ⊗s Y) ⊗s Y) ⊗s (Y ⊗s Y)) ⊗s (C 3)) ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1)) (transS (symS (left3 hx hy)) (transS (mulCong reflS (dCong (secondJet hx hy))) right3))

clearedJetODE : RamanujanX → RamanujanY → (scale (((+ 72) / 1) ⋆) ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1))) ≈s (((scale (((+ 108) / 1) ⋆) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ⊕s (scale (((+ 46) / 1) ⋆) ((((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f1))) ⊕s (scale (((+ 5) / 1) ⋆) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)))
clearedJetODE hx hy =
  (transS (F.scaleCong (+ 72 / 1) (symS (thirdJet hx hy))) (transS (transS (transS (scaleIsProduct ((+ 72) / 1) ((((Y ⊗s Y) ⊗s Y) ⊗s (Y ⊗s Y)) ⊗s (C 3))) (mulCong reflS (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS))) (transS (let open G.Solver in solve 2 (λ y c3 → (Κ ((+ 72) / 1) ⊗ ((((y ⊗ y) ⊗ y) ⊗ (y ⊗ y)) ⊗ c3)) ⊜ (Κ ((+ 72) / 1) ⊗ (((y ⊗ y) ⊗ y) ⊗ ((y ⊗ y) ⊗ c3)))) reflS Y (C 3)) (symS (transS (scaleIsProduct ((+ 72) / 1) (((Y ⊗s Y) ⊗s Y) ⊗s ((Y ⊗s Y) ⊗s (C 3)))) (mulCong reflS (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))))) (transS (F.scaleCong (+ 72 / 1) (mulCong reflS HR.clearedHyperRecurrence)) (transS (transS (transS (scaleIsProduct ((+ 72) / 1) (((Y ⊗s Y) ⊗s Y) ⊗s ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s (((scale (((+ 3) / 2) ⋆) (C 2)) ⊕s (scale (((+ 23) / 36) ⋆) (C 1))) ⊕s (scale (((+ 5) / 72) ⋆) f))))) (mulCong reflS (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (addCong (addCong (transS (scaleIsProduct ((+ 3) / 2) (C 2)) (mulCong reflS reflS)) (transS (scaleIsProduct ((+ 23) / 36) (C 1)) (mulCong reflS reflS))) (transS (scaleIsProduct ((+ 5) / 72) f) (mulCong reflS reflS))))))) (transS (let open G.Solver in solve 5 (λ y x c2 c1 f → (Κ ((+ 72) / 1) ⊗ (((y ⊗ y) ⊗ y) ⊗ ((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ (((Κ ((+ 3) / 2) ⊗ c2) ⊕ (Κ ((+ 23) / 36) ⊗ c1)) ⊕ (Κ ((+ 5) / 72) ⊗ f))))) ⊜ (((Κ ((+ 108) / 1) ⊗ ((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ (((y ⊗ y) ⊗ y) ⊗ c2))) ⊕ (Κ ((+ 46) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ c1))) ⊕ (Κ ((+ 5) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ f)))) reflS Y X (C 2) (C 1) f) (symS (addCong (addCong (transS (scaleIsProduct ((+ 108) / 1) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s (((Y ⊗s Y) ⊗s Y) ⊗s (C 2)))) (mulCong reflS (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong (mulCong reflS reflS) reflS) reflS)))) (transS (scaleIsProduct ((+ 46) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s (C 1))) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS)))) (transS (scaleIsProduct ((+ 5) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS))))))) (transS (addCong (addCong (F.scaleCong (+ 108 / 1) (mulCong reflS (secondJet hx hy))) (F.scaleCong (+ 46 / 1) (transS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS) (transS (let open G.Solver in solve 3 (λ x y c1 → (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ c1) ⊜ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ (y ⊗ y)) ⊗ (y ⊗ c1))) reflS X Y (C 1)) (symS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong reflS reflS)) (mulCong reflS reflS))))))) reflS) (transS (addCong (addCong reflS (F.scaleCong (+ 46 / 1) (mulCong reflS (chain0 hx hy)))) reflS) (transS (addCong (addCong (transS (scaleIsProduct ((+ 108) / 1) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) (mulCong reflS (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))) (transS (scaleIsProduct ((+ 46) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s (Y ⊗s Y)) ⊗s (X ⊗s f1))) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong reflS reflS)) (mulCong reflS reflS))))) (transS (scaleIsProduct ((+ 5) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS)))) (transS (let open G.Solver in solve 6 (λ x y v a u f → (((Κ ((+ 108) / 1) ⊗ ((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ a) ⊗ u)))) ⊕ (Κ ((+ 46) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ (y ⊗ y)) ⊗ (x ⊗ u)))) ⊕ (Κ ((+ 5) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ f))) ⊜ (((Κ ((+ 108) / 1) ⊗ ((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ a) ⊗ u)))) ⊕ (Κ ((+ 46) / 1) ⊗ ((((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ x) ⊗ (y ⊗ y)) ⊗ u))) ⊕ (Κ ((+ 5) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ f)))) reflS X Y f2 A f1 f) (symS (addCong (addCong (transS (scaleIsProduct ((+ 108) / 1) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) (mulCong reflS (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))) (transS (scaleIsProduct ((+ 46) / 1) ((((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f1)) (mulCong reflS (mulCong (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS) (mulCong reflS reflS)) reflS)))) (transS (scaleIsProduct ((+ 5) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS)))))))))))))

residualAsJet : U.residual f ≈s ((scale (((+ 72) / 1) ⋆) ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1))) ⊖s (((scale (((+ 108) / 1) ⋆) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ⊕s (scale (((+ 46) / 1) ⋆) ((((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f1))) ⊕s (scale (((+ 5) / 1) ⋆) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f))))
residualAsJet =
  transS (addCong (addCong (addCong
    (mulCong reflS (symS (F.dRepeat3 f)))
    (mulCong reflS (symS (F.dRepeat2 f)))) reflS)
    (mulCong (λ n → P.*-congʳ (P.≃-symm (P.⋆-distrib-neg (+ 5 / 1)))) reflS))
    (transS (addCong (addCong (addCong (mulCong (transS (scaleIsProduct ((+ 72) / 1) (((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y))) (mulCong reflS (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)))) reflS) (mulCong (transS (scaleIsProduct ((+ 108) / 1) (((X ⊗s X) ⊗s Y) ⊗s ((scale (((+ 2) / 1) ⋆) A) ⊖s (((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y))))) (mulCong reflS (mulCong (mulCong (mulCong reflS reflS) reflS) (subCong (transS (scaleIsProduct ((+ 2) / 1) A) (mulCong reflS reflS)) (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)))))) reflS)) (mulCong (subCong (subCong (transS (scaleIsProduct ((+ 72) / 1) (X ⊗s ((A ⊗s A) ⊕s (X ⊗s B)))) (mulCong reflS (mulCong reflS (addCong (mulCong reflS reflS) (mulCong reflS reflS))))) (transS (scaleIsProduct ((+ 108) / 1) ((X ⊗s (((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y))) ⊗s A)) (mulCong reflS (mulCong (mulCong reflS (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS))) reflS)))) (transS (scaleIsProduct ((+ 46) / 1) ((X ⊗s (Y ⊗s Y)) ⊗s (((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)))) (mulCong reflS (mulCong (mulCong reflS (mulCong reflS reflS)) (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)))))) reflS)) (mulCong (transS (scaleIsProduct ((Int.-_ (+ 5)) / 1) (((Y ⊗s Y) ⊗s Y) ⊗s (((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)))) (mulCong reflS (mulCong (mulCong (mulCong reflS reflS) reflS) (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS))))) reflS)) (transS (let open G.Solver in solve 8 (λ x y w a v b u f → (((((Κ ((+ 72) / 1) ⊗ (((x ⊗ x) ⊗ x) ⊗ (y ⊗ y))) ⊗ w) ⊕ ((Κ ((+ 108) / 1) ⊗ (((x ⊗ x) ⊗ y) ⊗ ((Κ ((+ 2) / 1) ⊗ a) ⊖ (((x ⊗ x) ⊗ x) ⊖ (y ⊗ y))))) ⊗ v)) ⊕ ((((Κ ((+ 72) / 1) ⊗ (x ⊗ ((a ⊗ a) ⊕ (x ⊗ b)))) ⊖ (Κ ((+ 108) / 1) ⊗ ((x ⊗ (((x ⊗ x) ⊗ x) ⊖ (y ⊗ y))) ⊗ a))) ⊖ (Κ ((+ 46) / 1) ⊗ ((x ⊗ (y ⊗ y)) ⊗ (((x ⊗ x) ⊗ x) ⊖ (y ⊗ y))))) ⊗ u)) ⊕ ((Κ ((Int.-_ (+ 5)) / 1) ⊗ (((y ⊗ y) ⊗ y) ⊗ (((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)))) ⊗ f)) ⊜ ((Κ ((+ 72) / 1) ⊗ ((((((x ⊗ x) ⊗ x) ⊗ (y ⊗ y)) ⊗ w) ⊕ (Κ ((+ 3) / 1) ⊗ ((((x ⊗ x) ⊗ y) ⊗ a) ⊗ v))) ⊕ ((x ⊗ ((a ⊗ a) ⊕ (x ⊗ b))) ⊗ u))) ⊖ (((Κ ((+ 108) / 1) ⊗ ((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((((x ⊗ x) ⊗ y) ⊗ v) ⊕ ((x ⊗ a) ⊗ u)))) ⊕ (Κ ((+ 46) / 1) ⊗ ((((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ x) ⊗ (y ⊗ y)) ⊗ u))) ⊕ (Κ ((+ 5) / 1) ⊗ (((((x ⊗ x) ⊗ x) ⊖ (y ⊗ y)) ⊗ ((y ⊗ y) ⊗ y)) ⊗ f))))) reflS X Y f3 A f2 B f1 f) (symS (subCong (transS (scaleIsProduct ((+ 72) / 1) ((((((X ⊗s X) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f3) ⊕s (scale (((+ 3) / 1) ⋆) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2))) ⊕s ((X ⊗s ((A ⊗s A) ⊕s (X ⊗s B))) ⊗s f1))) (mulCong reflS (addCong (addCong (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS) (transS (scaleIsProduct ((+ 3) / 1) ((((X ⊗s X) ⊗s Y) ⊗s A) ⊗s f2)) (mulCong reflS (mulCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) reflS)))) (mulCong (mulCong reflS (addCong (mulCong reflS reflS) (mulCong reflS reflS))) reflS)))) (addCong (addCong (transS (scaleIsProduct ((+ 108) / 1) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) (mulCong reflS (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (addCong (mulCong (mulCong (mulCong reflS reflS) reflS) reflS) (mulCong (mulCong reflS reflS) reflS))))) (transS (scaleIsProduct ((+ 46) / 1) ((((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f1)) (mulCong reflS (mulCong (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) reflS) (mulCong reflS reflS)) reflS)))) (transS (scaleIsProduct ((+ 5) / 1) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)) (mulCong reflS (mulCong (mulCong (subCong (mulCong (mulCong reflS reflS) reflS) (mulCong reflS reflS)) (mulCong (mulCong reflS reflS) reflS)) reflS))))))))

fSolution : RamanujanX → RamanujanY → U.Solution f
fSolution hx hy =
  transS residualAsJet
    (transS (subCong (clearedJetODE hx hy) reflS)
      (let open G.Solver in solve 1 (λ a → a ⊖ a ⊜ Κ 0ℚᵘ) reflS (((scale (((+ 108) / 1) ⋆) ((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((((X ⊗s X) ⊗s Y) ⊗s f2) ⊕s ((X ⊗s A) ⊗s f1)))) ⊕s (scale (((+ 46) / 1) ⋆) ((((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s X) ⊗s (Y ⊗s Y)) ⊗s f1))) ⊕s (scale (((+ 5) / 1) ⋆) (((((X ⊗s X) ⊗s X) ⊖s (Y ⊗s Y)) ⊗s ((Y ⊗s Y) ⊗s Y)) ⊗s f)))))

fIsHyper : f ≈s H.hyperCandidate
fIsHyper = composeOuterCong (H.weightedCoeff zero) H.hyperCoeff H.Zcoord
  (λ n → P.*-identityˡ (H.hyperCoeff n))

hyperSolution : RamanujanX → RamanujanY → U.Solution H.hyperCandidate
hyperSolution hx hy =
  transS (addCong (addCong (addCong
    (mulCong reflS (λ n → P.*-congˡ (symS fIsHyper n)))
    (mulCong reflS (λ n → P.*-congˡ (symS fIsHyper n))))
    (mulCong reflS (λ n → P.*-congˡ (symS fIsHyper n))))
    (mulCong reflS (symS fIsHyper))) (fSolution hx hy)

hyperSquare : RamanujanX → RamanujanY → RamanujanE →
  (H.hyperCandidate ⊗s H.hyperCandidate) ≈s X
hyperSquare hx hy he =
  T.hyperSquareFromFactor (F.factorizationFromRamanujan hx hy he H.hyperCandidate)
    (hyperSolution hx hy)

-- The jet is another readout of the same signed defect.
-- It is not a separately assumed analytic derivative identity.
jetIsHyper : C 1 ≈s H.hyperJetCandidate
jetIsHyper =
  composeOuterCong (H.weightedCoeff 1) H.hyperJetCoeff H.Zcoord
    (U.D1Meaning H.hyperCoeff)

hyperDFlow : RamanujanX → RamanujanY →
  (X ⊗s δ H.hyperCandidate) ≈s (Y ⊗s H.hyperJetCandidate)
hyperDFlow hx hy =
  transS (mulCong reflS (dCong (symS fIsHyper)))
    (transS (actualChain hx hy zero) (mulCong reflS jetIsHyper))

hyperFirst : RamanujanX → RamanujanY → RamanujanE →
  scale ((+ 2 / 1) ⋆) (Y ⊗s H.hyperJetCandidate) ≈s
    (δ X ⊗s H.hyperCandidate)
hyperFirst hx hy he =
  transS (F.scaleCong (+ 2 / 1) (symS (hyperDFlow hx hy)))
    (λ n →
      let a = scale ((+ 2 / 1) ⋆) (X ⊗s δ H.hyperCandidate) n
          b = (δ X ⊗s H.hyperCandidate) n
          h = T.defectFromODE H.hyperCandidate
            (F.factorizationFromRamanujan hx hy he H.hyperCandidate)
            (hyperSolution hx hy) n
          open P.ℝ-Solver
      in P.≃-trans (solve 2 (λ a b → a ⊜ (a ⊖ b) ⊕ b) P.≃-refl a b)
        (P.≃-trans (P.+-cong h P.≃-refl) (P.+-identityˡ b)))

hyperClearedJet : RamanujanX → RamanujanY → RamanujanE →
  scale ((+ 6 / 1) ⋆) (H.hyperCandidate ⊗s Y ⊗s H.hyperJetCandidate) ≈s
  scale ((+ 3 / 1) ⋆) (X ⊗s δ X)
hyperClearedJet hx hy he =
  let f = H.hyperCandidate
      j = H.hyperJetCandidate
      open G.Solver
  in transS (scaleIsProduct (+ 6 / 1) (f ⊗s Y ⊗s j))
    (transS (solve 3 (λ f y j → Κ (+ 6 / 1) ⊗ ((f ⊗ y) ⊗ j)
      ⊜ Κ (+ 3 / 1) ⊗ (f ⊗ (Κ (+ 2 / 1) ⊗ (y ⊗ j)))) reflS f Y j)
      (transS (mulCong reflS (mulCong reflS
        (transS (symS (scaleIsProduct (+ 2 / 1) (Y ⊗s j)))
          (hyperFirst hx hy he))))
        (transS (solve 2 (λ f dx → Κ (+ 3 / 1) ⊗ (f ⊗ (dx ⊗ f))
          ⊜ Κ (+ 3 / 1) ⊗ ((f ⊗ f) ⊗ dx)) reflS f (δ X))
          (transS (mulCong reflS (mulCong (hyperSquare hx hy he) reflS))
            (symS (scaleIsProduct (+ 3 / 1) (X ⊗s δ X)))))))
