module DASHI.Moonshine.CM163BishopHecke41ActualCrossExact where

-- SOURCE-WRITTEN, kernel pending. Exact finite elimination of the
-- remaining forty factors on the actual original Fin42 product.
-- No division by centered j or either colliding branch.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Res
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open Shift using (K; pComplement; sComplement)

-- A finite telescoping slope (no divided difference at x=0).
rest : ∀ {n} → (Fin n → BishopComplex) → BishopComplex → BishopComplex
rest c x = Prod.product (λ i → c i +C x)

slope : ∀ {n} → (Fin n → BishopComplex) → BishopComplex → BishopComplex
slope {zero} c x = A.zeroC
slope {suc n} c x = rest (λ i → c (Fin.suc i)) x +C
  (c Fin.zero *C slope (λ i → c (Fin.suc i)) x)

restAtZero : ∀ {n} (c : Fin n → BishopComplex) → rest c A.zeroC ≈C Prod.product c
restAtZero c = Prod.productCong _ _ (λ i → L.complexAddRightIdentity (c i))

restStep : ∀ a x u v → (((a +C x) *C u) -C (a *C v)) ≈C (x *C u +C a *C (u -C v))
restStep a x u v =
  (let open P.ℝ-Solver in solve 8 (λ ar ai xr xi ur ui vr vi → ((((ar ⊕ xr) ⊗ ur) ⊖ ((ai ⊕ xi) ⊗ ui)) ⊖ ((ar ⊗ vr) ⊖ (ai ⊗ vi))) ⊜ (((xr ⊗ ur) ⊖ (xi ⊗ ui)) ⊕ ((ar ⊗ (ur ⊖ vr)) ⊖ (ai ⊗ (ui ⊖ vi))))) P.≃-refl (C.re a) (C.im a) (C.re x) (C.im x) (C.re u) (C.im u) (C.re v) (C.im v)) ,
  (let open P.ℝ-Solver in solve 8 (λ ar ai xr xi ur ui vr vi → ((((ar ⊕ xr) ⊗ ui) ⊕ ((ai ⊕ xi) ⊗ ur)) ⊖ ((ar ⊗ vi) ⊕ (ai ⊗ vr))) ⊜ (((xr ⊗ ui) ⊕ (xi ⊗ ur)) ⊕ ((ar ⊗ (ui ⊖ vi)) ⊕ (ai ⊗ (ur ⊖ vr))))) P.≃-refl (C.re a) (C.im a) (C.re x) (C.im x) (C.re u) (C.im u) (C.re v) (C.im v))

restFinish : ∀ a x u t → (x *C u +C a *C (x *C t)) ≈C (x *C (u +C a *C t))
restFinish a x u t =
  (let open P.ℝ-Solver in solve 8 (λ ar ai xr xi ur ui tr ti → (((xr ⊗ ur) ⊖ (xi ⊗ ui)) ⊕ ((ar ⊗ ((xr ⊗ tr) ⊖ (xi ⊗ ti))) ⊖ (ai ⊗ ((xr ⊗ ti) ⊕ (xi ⊗ tr))))) ⊜ ((xr ⊗ (ur ⊕ ((ar ⊗ tr) ⊖ (ai ⊗ ti)))) ⊖ (xi ⊗ (ui ⊕ ((ar ⊗ ti) ⊕ (ai ⊗ tr)))))) P.≃-refl (C.re a) (C.im a) (C.re x) (C.im x) (C.re u) (C.im u) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 8 (λ ar ai xr xi ur ui tr ti → (((xr ⊗ ui) ⊕ (xi ⊗ ur)) ⊕ ((ar ⊗ ((xr ⊗ ti) ⊕ (xi ⊗ tr))) ⊕ (ai ⊗ ((xr ⊗ tr) ⊖ (xi ⊗ ti))))) ⊜ ((xr ⊗ (ui ⊕ ((ar ⊗ ti) ⊕ (ai ⊗ tr)))) ⊕ (xi ⊗ (ur ⊕ ((ar ⊗ tr) ⊖ (ai ⊗ ti)))))) P.≃-refl (C.re a) (C.im a) (C.re x) (C.im x) (C.re u) (C.im u) (C.re t) (C.im t))

zeroExpand : ∀ a b → a ≈C ((a -C b) +C b)
zeroExpand a b =
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ar ⊜ ((ar ⊖ br) ⊕ br)) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ai ⊜ ((ai ⊖ bi) ⊕ bi)) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b))

crossDistribute : ∀ n m p s x → ((n *C p -C m *C s) *C x) ≈C (n *C (x *C p) -C m *C (x *C s))
crossDistribute n m p s x =
  (let open P.ℝ-Solver in solve 10 (λ nr ni mr mi pr pi sr si xr xi → (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ xr) ⊖ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ xi)) ⊜ (((nr ⊗ ((xr ⊗ pr) ⊖ (xi ⊗ pi))) ⊖ (ni ⊗ ((xr ⊗ pi) ⊕ (xi ⊗ pr)))) ⊖ ((mr ⊗ ((xr ⊗ sr) ⊖ (xi ⊗ si))) ⊖ (mi ⊗ ((xr ⊗ si) ⊕ (xi ⊗ sr)))))) P.≃-refl (C.re n) (C.im n) (C.re m) (C.im m) (C.re p) (C.im p) (C.re s) (C.im s) (C.re x) (C.im x)) ,
  (let open P.ℝ-Solver in solve 10 (λ nr ni mr mi pr pi sr si xr xi → (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ xi) ⊕ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ xr)) ⊜ (((nr ⊗ ((xr ⊗ pi) ⊕ (xi ⊗ pr))) ⊕ (ni ⊗ ((xr ⊗ pr) ⊖ (xi ⊗ pi)))) ⊖ ((mr ⊗ ((xr ⊗ si) ⊕ (xi ⊗ sr))) ⊕ (mi ⊗ ((xr ⊗ sr) ⊖ (xi ⊗ si)))))) P.≃-refl (C.re n) (C.im n) (C.re m) (C.im m) (C.re p) (C.im p) (C.re s) (C.im s) (C.re x) (C.im x))

crossCollect : ∀ n m r s → (n *C (m *C r) -C m *C (n *C s)) ≈C ((n *C m) *C (r -C s))
crossCollect n m r s =
  (let open P.ℝ-Solver in solve 8 (λ nr ni mr mi rr ri sr si → (((nr ⊗ ((mr ⊗ rr) ⊖ (mi ⊗ ri))) ⊖ (ni ⊗ ((mr ⊗ ri) ⊕ (mi ⊗ rr)))) ⊖ ((mr ⊗ ((nr ⊗ sr) ⊖ (ni ⊗ si))) ⊖ (mi ⊗ ((nr ⊗ si) ⊕ (ni ⊗ sr))))) ⊜ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ (rr ⊖ sr)) ⊖ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ (ri ⊖ si)))) P.≃-refl (C.re n) (C.im n) (C.re m) (C.im m) (C.re r) (C.im r) (C.re s) (C.im s)) ,
  (let open P.ℝ-Solver in solve 8 (λ nr ni mr mi rr ri sr si → (((nr ⊗ ((mr ⊗ ri) ⊕ (mi ⊗ rr))) ⊕ (ni ⊗ ((mr ⊗ rr) ⊖ (mi ⊗ ri)))) ⊖ ((mr ⊗ ((nr ⊗ si) ⊕ (ni ⊗ sr))) ⊕ (mi ⊗ ((nr ⊗ sr) ⊖ (ni ⊗ si))))) ⊜ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ (ri ⊖ si)) ⊕ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ (rr ⊖ sr)))) P.≃-refl (C.re n) (C.im n) (C.re m) (C.im m) (C.re r) (C.im r) (C.re s) (C.im s))

tailRewrite : ∀ k y z → (y -C z) ≈C ((k -C z) +C (y -C k))
tailRewrite k y z =
  (let open P.ℝ-Solver in solve 6 (λ kr ki yr yi zr zi → (yr ⊖ zr) ⊜ ((kr ⊖ zr) ⊕ (yr ⊖ kr))) P.≃-refl (C.re k) (C.im k) (C.re y) (C.im y) (C.re z) (C.im z)) ,
  (let open P.ℝ-Solver in solve 6 (λ kr ki yr yi zr zi → (yi ⊖ zi) ⊜ ((ki ⊖ zi) ⊕ (yi ⊖ ki))) P.≃-refl (C.re k) (C.im k) (C.re y) (C.im y) (C.re z) (C.im z))

pairDifference : ∀ y k z → (y -C z) ≈C ((y -C k) -C (z -C k))
pairDifference y k z =
  (let open P.ℝ-Solver in solve 6 (λ yr yi kr ki zr zi → (yr ⊖ zr) ⊜ ((yr ⊖ kr) ⊖ (zr ⊖ kr))) P.≃-refl (C.re y) (C.im y) (C.re k) (C.im k) (C.re z) (C.im z)) ,
  (let open P.ℝ-Solver in solve 6 (λ yr yi kr ki zr zi → (yi ⊖ zi) ⊜ ((yi ⊖ ki) ⊖ (zi ⊖ ki))) P.≃-refl (C.re y) (C.im y) (C.re k) (C.im k) (C.re z) (C.im z))

splitReverse : ∀ a b t → (a *C (b *C t)) ≈C ((b *C a) *C t)
splitReverse a b t =
  (let open P.ℝ-Solver in solve 6 (λ ar ai br bi tr ti → ((ar ⊗ ((br ⊗ tr) ⊖ (bi ⊗ ti))) ⊖ (ai ⊗ ((br ⊗ ti) ⊕ (bi ⊗ tr)))) ⊜ ((((br ⊗ ar) ⊖ (bi ⊗ ai)) ⊗ tr) ⊖ (((br ⊗ ai) ⊕ (bi ⊗ ar)) ⊗ ti))) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 6 (λ ar ai br bi tr ti → ((ar ⊗ ((br ⊗ ti) ⊕ (bi ⊗ tr))) ⊕ (ai ⊗ ((br ⊗ tr) ⊖ (bi ⊗ ti)))) ⊜ ((((br ⊗ ar) ⊖ (bi ⊗ ai)) ⊗ ti) ⊕ (((br ⊗ ai) ⊕ (bi ⊗ ar)) ⊗ tr))) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b) (C.re t) (C.im t))

flipPair : ∀ k a b t → ((k -C a) *C ((k -C b) *C t)) ≈C (((b -C k) *C (a -C k)) *C t)
flipPair k a b t =
  (let open P.ℝ-Solver in solve 8 (λ kr ki ar ai br bi tr ti → (((kr ⊖ ar) ⊗ (((kr ⊖ br) ⊗ tr) ⊖ ((ki ⊖ bi) ⊗ ti))) ⊖ ((ki ⊖ ai) ⊗ (((kr ⊖ br) ⊗ ti) ⊕ ((ki ⊖ bi) ⊗ tr)))) ⊜ (((((br ⊖ kr) ⊗ (ar ⊖ kr)) ⊖ ((bi ⊖ ki) ⊗ (ai ⊖ ki))) ⊗ tr) ⊖ ((((br ⊖ kr) ⊗ (ai ⊖ ki)) ⊕ ((bi ⊖ ki) ⊗ (ar ⊖ kr))) ⊗ ti))) P.≃-refl (C.re k) (C.im k) (C.re a) (C.im a) (C.re b) (C.im b) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 8 (λ kr ki ar ai br bi tr ti → (((kr ⊖ ar) ⊗ (((kr ⊖ br) ⊗ ti) ⊕ ((ki ⊖ bi) ⊗ tr))) ⊕ ((ki ⊖ ai) ⊗ (((kr ⊖ br) ⊗ tr) ⊖ ((ki ⊖ bi) ⊗ ti)))) ⊜ (((((br ⊖ kr) ⊗ (ar ⊖ kr)) ⊖ ((bi ⊖ ki) ⊗ (ai ⊖ ki))) ⊗ ti) ⊕ ((((br ⊖ kr) ⊗ (ai ⊖ ki)) ⊕ ((bi ⊖ ki) ⊗ (ar ⊖ kr))) ⊗ tr))) P.≃-refl (C.re k) (C.im k) (C.re a) (C.im a) (C.re b) (C.im b) (C.re t) (C.im t))

normalizeLeft : ∀ w n m p s x → (((((w *C w) *C n) *C p) -C (((w *C w) *C m) *C s)) *C powC (w *C x) 2) ≈C (((w *C w) *C (w *C w)) *C ((n *C p -C m *C s) *C powC x 2))
normalizeLeft w n m p s x =
  (let open P.ℝ-Solver in solve 12 (λ wr wi nr ni mr mi pr pi sr si xr xi → (((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ pr) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ pi)) ⊖ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)) ⊗ sr) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)) ⊗ si))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 1ℚᵘ) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 0ℚᵘ))) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 0ℚᵘ) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 1ℚᵘ))))) ⊖ ((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ pi) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ pr)) ⊖ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)) ⊗ si) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)) ⊗ sr))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 0ℚᵘ) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 1ℚᵘ))) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 1ℚᵘ) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 0ℚᵘ)))))) ⊜ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi))) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))) ⊗ (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ ((xr ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))) ⊖ (xi ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))))) ⊖ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ ((xr ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))) ⊕ (xi ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))))))) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr))) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))) ⊗ (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ ((xr ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))) ⊕ (xi ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))))) ⊕ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ ((xr ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))) ⊖ (xi ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))))))))) P.≃-refl (C.re w) (C.im w) (C.re n) (C.im n) (C.re m) (C.im m) (C.re p) (C.im p) (C.re s) (C.im s) (C.re x) (C.im x)) ,
  (let open P.ℝ-Solver in solve 12 (λ wr wi nr ni mr mi pr pi sr si xr xi → (((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ pr) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ pi)) ⊖ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)) ⊗ sr) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)) ⊗ si))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 0ℚᵘ) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 1ℚᵘ))) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 1ℚᵘ) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 0ℚᵘ))))) ⊕ ((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ pi) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ pr)) ⊖ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)) ⊗ si) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)) ⊗ sr))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 1ℚᵘ) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 0ℚᵘ))) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ Κ 0ℚᵘ) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ Κ 1ℚᵘ)))))) ⊜ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi))) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))) ⊗ (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ ((xr ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))) ⊕ (xi ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))))) ⊕ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ ((xr ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))) ⊖ (xi ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))))))) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr))) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))) ⊗ (((((nr ⊗ pr) ⊖ (ni ⊗ pi)) ⊖ ((mr ⊗ sr) ⊖ (mi ⊗ si))) ⊗ ((xr ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))) ⊖ (xi ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))))) ⊖ ((((nr ⊗ pi) ⊕ (ni ⊗ pr)) ⊖ ((mr ⊗ si) ⊕ (mi ⊗ sr))) ⊗ ((xr ⊗ ((xr ⊗ Κ 0ℚᵘ) ⊕ (xi ⊗ Κ 1ℚᵘ))) ⊕ (xi ⊗ ((xr ⊗ Κ 1ℚᵘ) ⊖ (xi ⊗ Κ 0ℚᵘ))))))))) P.≃-refl (C.re w) (C.im w) (C.re n) (C.im n) (C.re m) (C.im m) (C.re p) (C.im p) (C.re s) (C.im s) (C.re x) (C.im x))

normalizeRight : ∀ w n m x t → (((((w *C w) *C n) *C ((w *C w) *C m))) *C ((w *C x) *C t)) ≈C (((w *C w) *C (w *C w)) *C ((n *C m) *C (x *C (w *C t))))
normalizeRight w n m x t =
  (let open P.ℝ-Solver in solve 10 (λ wr wi nr ni mr mi xr xi tr ti → ((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi))) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ tr) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ti))) ⊖ (((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr))) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ti) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ tr)))) ⊜ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi))) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))) ⊗ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ ((xr ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))) ⊖ (xi ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))))) ⊖ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ ((xr ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))) ⊕ (xi ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))))))) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr))) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))) ⊗ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ ((xr ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))) ⊕ (xi ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))))) ⊕ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ ((xr ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))) ⊖ (xi ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))))))))) P.≃-refl (C.re w) (C.im w) (C.re n) (C.im n) (C.re m) (C.im m) (C.re x) (C.im x) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 10 (λ wr wi nr ni mr mi xr xi tr ti → ((((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi))) ⊖ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr)))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ ti) ⊕ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ tr))) ⊕ (((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ nr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ni)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mi) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mr))) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ni) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ nr)) ⊗ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ mr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ mi)))) ⊗ ((((wr ⊗ xr) ⊖ (wi ⊗ xi)) ⊗ tr) ⊖ (((wr ⊗ xi) ⊕ (wi ⊗ xr)) ⊗ ti)))) ⊜ ((((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi))) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))) ⊗ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ ((xr ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))) ⊕ (xi ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))))) ⊕ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ ((xr ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))) ⊖ (xi ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))))))) ⊕ (((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr))) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))) ⊗ ((((nr ⊗ mr) ⊖ (ni ⊗ mi)) ⊗ ((xr ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))) ⊖ (xi ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))))) ⊖ (((nr ⊗ mi) ⊕ (ni ⊗ mr)) ⊗ ((xr ⊗ ((wr ⊗ ti) ⊕ (wi ⊗ tr))) ⊕ (xi ⊗ ((wr ⊗ tr) ⊖ (wi ⊗ ti))))))))) P.≃-refl (C.re w) (C.im w) (C.re n) (C.im n) (C.re m) (C.im m) (C.re x) (C.im x) (C.re t) (C.im t))


restDifference : ∀ {n} (c : Fin n → BishopComplex) x →
  (rest c x -C Prod.product c) ≈C (x *C slope c x)
restDifference {zero} c x = complexTrans (Prod.differenceSelf A.oneC) (complexSym (L.complexMultiplyRightZero x))
restDifference {suc n} c x =
  let a = c Fin.zero
      cs = λ i → c (Fin.suc i)
      u = rest cs x
      v = Prod.product cs
      t = slope cs x
  in complexTrans (restStep a x u v)
    (complexTrans (A.addCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (restDifference cs x)))
      (restFinish a x u t))

zeroDifference : ∀ a b → (a -C b) ≈C A.zeroC → a ≈C b
zeroDifference a b h = complexTrans (zeroExpand a b)
  (complexTrans (A.addCCongruent h (C.≈C-refl _)) (L.complexAddLeftIdentity b))

-- Eliminate the remainder using only the two product equalities.
crossAlgebra : ∀ x n m p s r1 r0 t →
  (powC x 2 *C p) ≈C (m *C r1) →
  (powC x 2 *C s) ≈C (n *C r0) →
  (r1 -C r0) ≈C (x *C t) →
  ((n *C p -C m *C s) *C powC x 2) ≈C ((n *C m) *C (x *C t))
crossAlgebra x n m p s r1 r0 t hp hs ht =
  complexTrans (crossDistribute n m p s (powC x 2))
    (complexTrans (A.subCCongruent (A.mulCCongruent (C.≈C-refl _) hp)
      (A.mulCCongruent (C.≈C-refl _) hs))
      (complexTrans (crossCollect n m r1 r0) (A.mulCCongruent (C.≈C-refl _) ht)))

module At (inputs : Round11.BishopCutset) where
  module R = Res.At inputs
  module G = R.G

  chart : ∀ p → Fin 42 → BishopComplex
  chart p i = G.j (Chart.chartPoint i p)

  x xp xm : ∀ p → BishopComplex
  x p = G.j p -C K
  xp p = chart p (Fin.suc Fin.zero) -C K
  xm p = chart p Fin.zero -C K

  n m : ∀ p → BishopComplex
  n p = xp p *C xm p
  m p = (x p -C xp p) *C (x p -C xm p)

  c : ∀ p → Fin 40 → BishopComplex
  c p i = K -C chart p (Fin.suc (Fin.suc i))

  tailAt : ∀ p y → Prod.product (λ i → y -C chart p (Fin.suc (Fin.suc i))) ≈C
    rest (c p) (y -C K)
  tailAt p y = Prod.productCong _ _ (λ i → tailRewrite K y (chart p (Fin.suc (Fin.suc i))))

  splitDiagonal : ∀ p → G.diagonal p ≈C (m p *C rest (c p) (x p))
  splitDiagonal p =
    complexTrans (A.mulCCongruent (pairDifference (G.j p) K (chart p Fin.zero))
      (A.mulCCongruent (pairDifference (G.j p) K (chart p (Fin.suc Fin.zero))) (tailAt p (G.j p))))
      (splitReverse (x p -C xm p) (x p -C xp p) (rest (c p) (x p)))

  splitSlice : ∀ p → G.product p K ≈C (n p *C Prod.product (c p))
  splitSlice p = flipPair K (chart p Fin.zero) (chart p (Fin.suc Fin.zero)) (Prod.product (c p))

  -- These are the actual global residuals constructed in the prior cut.
  -- Rigidity supplies their vanishing, not a new abstract Hecke product.
  actualCross : ∀ p → R.d p ≈C A.zeroC → R.s p ≈C A.zeroC →
    ((n p *C pComplement (x p) -C m p *C sComplement (x p)) *C powC (x p) 2) ≈C
      ((n p *C m p) *C (x p *C slope (c p) (x p)))
  actualCross p hd hs = crossAlgebra (x p) (n p) (m p) (pComplement (x p)) (sComplement (x p))
    (rest (c p) (x p)) (Prod.product (c p)) (slope (c p) (x p))
    (complexTrans (complexSym (Shift.diagonalFactor (G.j p)))
      (complexTrans (complexSym (zeroDifference _ _ hd)) (splitDiagonal p)))
    (complexTrans (complexSym (Shift.sliceFactor (G.j p)))
      (complexTrans (complexSym (zeroDifference _ _ hs)) (splitSlice p)))
    (restDifference (c p) (x p))

  -- Coordinate normalization, valid at every nonzero w. No branch
  -- apartness is used. At w=0 the existing literal quadratic relation
  -- supplies the zero-mode equation separately.
  normalizedCross : ∀ p w X Xp Xm → Rec.BishopComplexNonzero w →
    x p ≈C (w *C X) → xp p ≈C (w *C Xp) → xm p ≈C (w *C Xm) →
    R.d p ≈C A.zeroC → R.s p ≈C A.zeroC →
    let N0 = Xp *C Xm
        M0 = (X -C Xp) *C (X -C Xm)
        T = slope (c p) (x p)
    in ((N0 *C pComplement (x p) -C M0 *C sComplement (x p)) *C powC X 2) ≈C
       ((N0 *C M0) *C (X *C (w *C T)))
  normalizedCross p w X Xp Xm nz hx hp hm hd hs =
    let N0 = Xp *C Xm; M0 = (X -C Xp) *C (X -C Xm)
        P0 = pComplement (x p); S0 = sComplement (x p); T = slope (c p) (x p)
        nRead = complexTrans (A.mulCCongruent hp hm) (Alg.shuffle w Xp w Xm)
        mRead = complexTrans (A.mulCCongruent
          (complexTrans (A.subCCongruent hx hp) (complexSym (Alg.mulSub w X Xp)))
          (complexTrans (A.subCCongruent hx hm) (complexSym (Alg.mulSub w X Xm))))
          (Alg.shuffle w (X -C Xp) w (X -C Xm))
        left = complexTrans (A.mulCCongruent
          (A.subCCongruent (A.mulCCongruent nRead (C.≈C-refl _))
            (A.mulCCongruent mRead (C.≈C-refl _)))
          (A.powCCongruent hx 2))
          (normalizeLeft w N0 M0 P0 S0 X)
        right = complexTrans (A.mulCCongruent (A.mulCCongruent nRead mRead)
          (A.mulCCongruent hx (C.≈C-refl _))) (normalizeRight w N0 M0 X T)
        w4 = (w *C w) *C (w *C w)
    in J.cancelLeft w4 _ _ (J.nonzeroMul (J.nonzeroMul nz nz) (J.nonzeroMul nz nz))
      (complexTrans (complexSym left) (complexTrans (actualCross p hd hs) right))
