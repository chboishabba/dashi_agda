module DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Actual Bishop-complex rational row functions. Classical even-power
-- Lipschitz summation is reduced to a dyadic distribution identity and
-- an original-exponential small-argument limit, not a new cotangent axiom.
-- X(q)=q/(1-q)^2. Retain both signed half-phase sheets q and -q.
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)

negC : BishopComplex → BishopComplex
negC (C.complex x y) = C.complex (R.- x) (R.- y)

scale : Nat → BishopComplex → BishopComplex
scale n = A.scaleC (R._⋆ (+ n / 1))

negCong : ∀ {a b} → a ≈C b → negC a ≈C negC b
negCong {C.complex _ _} {C.complex _ _} (a , b) = P.-‿cong a , P.-‿cong b

scaleCong : ∀ n {a b} → a ≈C b → scale n a ≈C scale n b
scaleCong n h = A.scaleCCongruent h (R._⋆ (+ n / 1))

gapMinus gapPlus gapSquared : BishopComplex → BishopComplex
gapMinus q = A.oneC -C q
gapPlus q = A.oneC +C q
gapSquared q = A.oneC -C (q *C q)

X : (q : BishopComplex) → Rec.BishopComplexNonzero (gapMinus q) → BishopComplex
X q nz = let i = Rec.reciprocalC (gapMinus q) nz in q *C (i *C i)

P4 P6 : BishopComplex → BishopComplex
P4 u = u +C scale 6 (u *C u)
P6 u = (u +C scale 30 (u *C u)) +C scale 120 (u *C (u *C u))

sym4 sym6 : BishopComplex → BishopComplex → BishopComplex
sym4 s p = s +C scale 6 ((s *C s) -C scale 2 p)
sym6 s p = (s +C scale 30 ((s *C s) -C scale 2 p)) +C
  scale 120 ((s *C (s *C s)) -C scale 3 (p *C s))

gapFactor : ∀ q → ((A.oneC -C q) *C (A.oneC +C q)) ≈C (A.oneC -C (q *C q))
gapFactor (C.complex qr qi) =
  (let open P.ℝ-Solver in
    solve 2 (λ qr qi → (((Κ (+ 1 / 1) ⊖ qr) ⊗ (Κ (+ 1 / 1) ⊕ qr)) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ (Κ (+ 0 / 1) ⊕ qi)))
      ⊜ (Κ (+ 1 / 1) ⊖ ((qr ⊗ qr) ⊖ (qi ⊗ qi)))) P.≃-refl qr qi)
  ,
  (let open P.ℝ-Solver in
    solve 2 (λ qr qi → (((Κ (+ 1 / 1) ⊖ qr) ⊗ (Κ (+ 0 / 1) ⊕ qi)) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ (Κ (+ 1 / 1) ⊕ qr)))
      ⊜ (Κ (+ 0 / 1) ⊖ ((qr ⊗ qi) ⊕ (qi ⊗ qr)))) P.≃-refl qr qi)

gapMinusNeg : ∀ q → (A.oneC -C (negC q)) ≈C (A.oneC +C q)
gapMinusNeg (C.complex qr qi) =
  (let open P.ℝ-Solver in
    solve 2 (λ qr qi → (Κ (+ 1 / 1) ⊖ (⊝ qr))
      ⊜ (Κ (+ 1 / 1) ⊕ qr)) P.≃-refl qr qi)
  ,
  (let open P.ℝ-Solver in
    solve 2 (λ qr qi → (Κ (+ 0 / 1) ⊖ (⊝ qi))
      ⊜ (Κ (+ 0 / 1) ⊕ qi)) P.≃-refl qr qi)

sumWithCommonInverse : ∀ q c → ((q *C (((A.oneC +C q) *C c) *C ((A.oneC +C q) *C c))) +C ((negC q) *C (((A.oneC -C q) *C c) *C ((A.oneC -C q) *C c)))) ≈C (scale 4 ((q *C q) *C (c *C c)))
sumWithCommonInverse (C.complex qr qi) (C.complex cr ci) =
  (let open P.ℝ-Solver in
    solve 4 (λ qr qi cr ci → (((qr ⊗ (((((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci))) ⊖ ((((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr))))) ⊖ (qi ⊗ (((((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr))) ⊕ ((((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci)))))) ⊕ (((⊝ qr) ⊗ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci))) ⊖ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr))))) ⊖ ((⊝ qi) ⊗ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr))) ⊕ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci)))))))
      ⊜ (Κ (+ 4 / 1) ⊗ ((((qr ⊗ qr) ⊖ (qi ⊗ qi)) ⊗ ((cr ⊗ cr) ⊖ (ci ⊗ ci))) ⊖ (((qr ⊗ qi) ⊕ (qi ⊗ qr)) ⊗ ((cr ⊗ ci) ⊕ (ci ⊗ cr)))))) P.≃-refl qr qi cr ci)
  ,
  (let open P.ℝ-Solver in
    solve 4 (λ qr qi cr ci → (((qr ⊗ (((((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr))) ⊕ ((((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci))))) ⊕ (qi ⊗ (((((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ ci))) ⊖ ((((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ cr)))))) ⊕ (((⊝ qr) ⊗ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr))) ⊕ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci))))) ⊕ ((⊝ qi) ⊗ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ cr) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ci))) ⊖ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr)) ⊗ (((Κ (+ 1 / 1) ⊖ qr) ⊗ ci) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ cr)))))))
      ⊜ (Κ (+ 4 / 1) ⊗ ((((qr ⊗ qr) ⊖ (qi ⊗ qi)) ⊗ ((cr ⊗ ci) ⊕ (ci ⊗ cr))) ⊕ (((qr ⊗ qi) ⊕ (qi ⊗ qr)) ⊗ ((cr ⊗ cr) ⊖ (ci ⊗ ci)))))) P.≃-refl qr qi cr ci)

productReassociate : ∀ q a b → ((q *C (a *C a)) *C ((negC q) *C (b *C b))) ≈C (negC ((q *C q) *C ((a *C b) *C (a *C b))))
productReassociate (C.complex qr qi) (C.complex ar ai) (C.complex br bi) =
  (let open P.ℝ-Solver in
    solve 6 (λ qr qi ar ai br bi → ((((qr ⊗ ((ar ⊗ ar) ⊖ (ai ⊗ ai))) ⊖ (qi ⊗ ((ar ⊗ ai) ⊕ (ai ⊗ ar)))) ⊗ (((⊝ qr) ⊗ ((br ⊗ br) ⊖ (bi ⊗ bi))) ⊖ ((⊝ qi) ⊗ ((br ⊗ bi) ⊕ (bi ⊗ br))))) ⊖ (((qr ⊗ ((ar ⊗ ai) ⊕ (ai ⊗ ar))) ⊕ (qi ⊗ ((ar ⊗ ar) ⊖ (ai ⊗ ai)))) ⊗ (((⊝ qr) ⊗ ((br ⊗ bi) ⊕ (bi ⊗ br))) ⊕ ((⊝ qi) ⊗ ((br ⊗ br) ⊖ (bi ⊗ bi))))))
      ⊜ (⊝ ((((qr ⊗ qr) ⊖ (qi ⊗ qi)) ⊗ ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi))) ⊖ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br))))) ⊖ (((qr ⊗ qi) ⊕ (qi ⊗ qr)) ⊗ ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br))) ⊕ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi)))))))) P.≃-refl qr qi ar ai br bi)
  ,
  (let open P.ℝ-Solver in
    solve 6 (λ qr qi ar ai br bi → ((((qr ⊗ ((ar ⊗ ar) ⊖ (ai ⊗ ai))) ⊖ (qi ⊗ ((ar ⊗ ai) ⊕ (ai ⊗ ar)))) ⊗ (((⊝ qr) ⊗ ((br ⊗ bi) ⊕ (bi ⊗ br))) ⊕ ((⊝ qi) ⊗ ((br ⊗ br) ⊖ (bi ⊗ bi))))) ⊕ (((qr ⊗ ((ar ⊗ ai) ⊕ (ai ⊗ ar))) ⊕ (qi ⊗ ((ar ⊗ ar) ⊖ (ai ⊗ ai)))) ⊗ (((⊝ qr) ⊗ ((br ⊗ br) ⊖ (bi ⊗ bi))) ⊖ ((⊝ qi) ⊗ ((br ⊗ bi) ⊕ (bi ⊗ br))))))
      ⊜ (⊝ ((((qr ⊗ qr) ⊖ (qi ⊗ qi)) ⊗ ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br))) ⊕ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi))))) ⊕ (((qr ⊗ qi) ⊕ (qi ⊗ qr)) ⊗ ((((ar ⊗ br) ⊖ (ai ⊗ bi)) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi))) ⊖ (((ar ⊗ bi) ⊕ (ai ⊗ br)) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br)))))))) P.≃-refl qr qi ar ai br bi)

inversePairReassociate : ∀ q a b → ((A.oneC -C (q *C q)) *C (a *C b)) ≈C (((A.oneC -C q) *C a) *C ((A.oneC +C q) *C b))
inversePairReassociate (C.complex qr qi) (C.complex ar ai) (C.complex br bi) =
  (let open P.ℝ-Solver in
    solve 6 (λ qr qi ar ai br bi → (((Κ (+ 1 / 1) ⊖ ((qr ⊗ qr) ⊖ (qi ⊗ qi))) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi))) ⊖ ((Κ (+ 0 / 1) ⊖ ((qr ⊗ qi) ⊕ (qi ⊗ qr))) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br))))
      ⊜ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ ar) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ai)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ br) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ bi))) ⊖ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ai) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ar)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ bi) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ br))))) P.≃-refl qr qi ar ai br bi)
  ,
  (let open P.ℝ-Solver in
    solve 6 (λ qr qi ar ai br bi → (((Κ (+ 1 / 1) ⊖ ((qr ⊗ qr) ⊖ (qi ⊗ qi))) ⊗ ((ar ⊗ bi) ⊕ (ai ⊗ br))) ⊕ ((Κ (+ 0 / 1) ⊖ ((qr ⊗ qi) ⊕ (qi ⊗ qr))) ⊗ ((ar ⊗ br) ⊖ (ai ⊗ bi))))
      ⊜ (((((Κ (+ 1 / 1) ⊖ qr) ⊗ ar) ⊖ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ai)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ bi) ⊕ ((Κ (+ 0 / 1) ⊕ qi) ⊗ br))) ⊕ ((((Κ (+ 1 / 1) ⊖ qr) ⊗ ai) ⊕ ((Κ (+ 0 / 1) ⊖ qi) ⊗ ar)) ⊗ (((Κ (+ 1 / 1) ⊕ qr) ⊗ br) ⊖ ((Κ (+ 0 / 1) ⊕ qi) ⊗ bi))))) P.≃-refl qr qi ar ai br bi)

symmetric4 : ∀ u v → ((u +C (scale 6 (u *C u))) +C (v +C (scale 6 (v *C v)))) ≈C ((u +C v) +C (scale 6 (((u +C v) *C (u +C v)) -C (scale 2 (u *C v)))))
symmetric4 (C.complex ur ui) (C.complex vr vi) =
  (let open P.ℝ-Solver in
    solve 4 (λ ur ui vr vi → ((ur ⊕ (Κ (+ 6 / 1) ⊗ ((ur ⊗ ur) ⊖ (ui ⊗ ui)))) ⊕ (vr ⊕ (Κ (+ 6 / 1) ⊗ ((vr ⊗ vr) ⊖ (vi ⊗ vi)))))
      ⊜ ((ur ⊕ vr) ⊕ (Κ (+ 6 / 1) ⊗ ((((ur ⊕ vr) ⊗ (ur ⊕ vr)) ⊖ ((ui ⊕ vi) ⊗ (ui ⊕ vi))) ⊖ (Κ (+ 2 / 1) ⊗ ((ur ⊗ vr) ⊖ (ui ⊗ vi))))))) P.≃-refl ur ui vr vi)
  ,
  (let open P.ℝ-Solver in
    solve 4 (λ ur ui vr vi → ((ui ⊕ (Κ (+ 6 / 1) ⊗ ((ur ⊗ ui) ⊕ (ui ⊗ ur)))) ⊕ (vi ⊕ (Κ (+ 6 / 1) ⊗ ((vr ⊗ vi) ⊕ (vi ⊗ vr)))))
      ⊜ ((ui ⊕ vi) ⊕ (Κ (+ 6 / 1) ⊗ ((((ur ⊕ vr) ⊗ (ui ⊕ vi)) ⊕ ((ui ⊕ vi) ⊗ (ur ⊕ vr))) ⊖ (Κ (+ 2 / 1) ⊗ ((ur ⊗ vi) ⊕ (ui ⊗ vr))))))) P.≃-refl ur ui vr vi)

symmetric6 : ∀ u v → (((u +C (scale 30 (u *C u))) +C (scale 120 (u *C (u *C u)))) +C ((v +C (scale 30 (v *C v))) +C (scale 120 (v *C (v *C v))))) ≈C (((u +C v) +C (scale 30 (((u +C v) *C (u +C v)) -C (scale 2 (u *C v))))) +C (scale 120 (((u +C v) *C ((u +C v) *C (u +C v))) -C (scale 3 ((u *C v) *C (u +C v))))))
symmetric6 (C.complex ur ui) (C.complex vr vi) =
  (let open P.ℝ-Solver in
    solve 4 (λ ur ui vr vi → (((ur ⊕ (Κ (+ 30 / 1) ⊗ ((ur ⊗ ur) ⊖ (ui ⊗ ui)))) ⊕ (Κ (+ 120 / 1) ⊗ ((ur ⊗ ((ur ⊗ ur) ⊖ (ui ⊗ ui))) ⊖ (ui ⊗ ((ur ⊗ ui) ⊕ (ui ⊗ ur)))))) ⊕ ((vr ⊕ (Κ (+ 30 / 1) ⊗ ((vr ⊗ vr) ⊖ (vi ⊗ vi)))) ⊕ (Κ (+ 120 / 1) ⊗ ((vr ⊗ ((vr ⊗ vr) ⊖ (vi ⊗ vi))) ⊖ (vi ⊗ ((vr ⊗ vi) ⊕ (vi ⊗ vr)))))))
      ⊜ (((ur ⊕ vr) ⊕ (Κ (+ 30 / 1) ⊗ ((((ur ⊕ vr) ⊗ (ur ⊕ vr)) ⊖ ((ui ⊕ vi) ⊗ (ui ⊕ vi))) ⊖ (Κ (+ 2 / 1) ⊗ ((ur ⊗ vr) ⊖ (ui ⊗ vi)))))) ⊕ (Κ (+ 120 / 1) ⊗ ((((ur ⊕ vr) ⊗ (((ur ⊕ vr) ⊗ (ur ⊕ vr)) ⊖ ((ui ⊕ vi) ⊗ (ui ⊕ vi)))) ⊖ ((ui ⊕ vi) ⊗ (((ur ⊕ vr) ⊗ (ui ⊕ vi)) ⊕ ((ui ⊕ vi) ⊗ (ur ⊕ vr))))) ⊖ (Κ (+ 3 / 1) ⊗ ((((ur ⊗ vr) ⊖ (ui ⊗ vi)) ⊗ (ur ⊕ vr)) ⊖ (((ur ⊗ vi) ⊕ (ui ⊗ vr)) ⊗ (ui ⊕ vi)))))))) P.≃-refl ur ui vr vi)
  ,
  (let open P.ℝ-Solver in
    solve 4 (λ ur ui vr vi → (((ui ⊕ (Κ (+ 30 / 1) ⊗ ((ur ⊗ ui) ⊕ (ui ⊗ ur)))) ⊕ (Κ (+ 120 / 1) ⊗ ((ur ⊗ ((ur ⊗ ui) ⊕ (ui ⊗ ur))) ⊕ (ui ⊗ ((ur ⊗ ur) ⊖ (ui ⊗ ui)))))) ⊕ ((vi ⊕ (Κ (+ 30 / 1) ⊗ ((vr ⊗ vi) ⊕ (vi ⊗ vr)))) ⊕ (Κ (+ 120 / 1) ⊗ ((vr ⊗ ((vr ⊗ vi) ⊕ (vi ⊗ vr))) ⊕ (vi ⊗ ((vr ⊗ vr) ⊖ (vi ⊗ vi)))))))
      ⊜ (((ui ⊕ vi) ⊕ (Κ (+ 30 / 1) ⊗ ((((ur ⊕ vr) ⊗ (ui ⊕ vi)) ⊕ ((ui ⊕ vi) ⊗ (ur ⊕ vr))) ⊖ (Κ (+ 2 / 1) ⊗ ((ur ⊗ vi) ⊕ (ui ⊗ vr)))))) ⊕ (Κ (+ 120 / 1) ⊗ ((((ur ⊕ vr) ⊗ (((ur ⊕ vr) ⊗ (ui ⊕ vi)) ⊕ ((ui ⊕ vi) ⊗ (ur ⊕ vr)))) ⊕ ((ui ⊕ vi) ⊗ (((ur ⊕ vr) ⊗ (ur ⊕ vr)) ⊖ ((ui ⊕ vi) ⊗ (ui ⊕ vi))))) ⊖ (Κ (+ 3 / 1) ⊗ ((((ur ⊗ vr) ⊖ (ui ⊗ vi)) ⊗ (ui ⊕ vi)) ⊕ (((ur ⊗ vi) ⊕ (ui ⊗ vr)) ⊗ (ur ⊕ vr)))))))) P.≃-refl ur ui vr vi)

scaled4 : ∀ w → ((scale 4 w) +C (scale 6 (((scale 4 w) *C (scale 4 w)) -C (scale 2 (negC w))))) ≈C (scale 16 (w +C (scale 6 (w *C w))))
scaled4 (C.complex wr wi) =
  (let open P.ℝ-Solver in
    solve 2 (λ wr wi → ((Κ (+ 4 / 1) ⊗ wr) ⊕ (Κ (+ 6 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wr)) ⊖ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wi))) ⊖ (Κ (+ 2 / 1) ⊗ (⊝ wr)))))
      ⊜ (Κ (+ 16 / 1) ⊗ (wr ⊕ (Κ (+ 6 / 1) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))))) P.≃-refl wr wi)
  ,
  (let open P.ℝ-Solver in
    solve 2 (λ wr wi → ((Κ (+ 4 / 1) ⊗ wi) ⊕ (Κ (+ 6 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wi)) ⊕ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wr))) ⊖ (Κ (+ 2 / 1) ⊗ (⊝ wi)))))
      ⊜ (Κ (+ 16 / 1) ⊗ (wi ⊕ (Κ (+ 6 / 1) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))))) P.≃-refl wr wi)

scaled6 : ∀ w → (((scale 4 w) +C (scale 30 (((scale 4 w) *C (scale 4 w)) -C (scale 2 (negC w))))) +C (scale 120 (((scale 4 w) *C ((scale 4 w) *C (scale 4 w))) -C (scale 3 ((negC w) *C (scale 4 w)))))) ≈C (scale 64 ((w +C (scale 30 (w *C w))) +C (scale 120 (w *C (w *C w)))))
scaled6 (C.complex wr wi) =
  (let open P.ℝ-Solver in
    solve 2 (λ wr wi → (((Κ (+ 4 / 1) ⊗ wr) ⊕ (Κ (+ 30 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wr)) ⊖ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wi))) ⊖ (Κ (+ 2 / 1) ⊗ (⊝ wr))))) ⊕ (Κ (+ 120 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wr)) ⊖ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wi)))) ⊖ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wi)) ⊕ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wr))))) ⊖ (Κ (+ 3 / 1) ⊗ (((⊝ wr) ⊗ (Κ (+ 4 / 1) ⊗ wr)) ⊖ ((⊝ wi) ⊗ (Κ (+ 4 / 1) ⊗ wi)))))))
      ⊜ (Κ (+ 64 / 1) ⊗ ((wr ⊕ (Κ (+ 30 / 1) ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))) ⊕ (Κ (+ 120 / 1) ⊗ ((wr ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi))) ⊖ (wi ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))))))) P.≃-refl wr wi)
  ,
  (let open P.ℝ-Solver in
    solve 2 (λ wr wi → (((Κ (+ 4 / 1) ⊗ wi) ⊕ (Κ (+ 30 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wi)) ⊕ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wr))) ⊖ (Κ (+ 2 / 1) ⊗ (⊝ wi))))) ⊕ (Κ (+ 120 / 1) ⊗ ((((Κ (+ 4 / 1) ⊗ wr) ⊗ (((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wi)) ⊕ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wr)))) ⊕ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (((Κ (+ 4 / 1) ⊗ wr) ⊗ (Κ (+ 4 / 1) ⊗ wr)) ⊖ ((Κ (+ 4 / 1) ⊗ wi) ⊗ (Κ (+ 4 / 1) ⊗ wi))))) ⊖ (Κ (+ 3 / 1) ⊗ (((⊝ wr) ⊗ (Κ (+ 4 / 1) ⊗ wi)) ⊕ ((⊝ wi) ⊗ (Κ (+ 4 / 1) ⊗ wr)))))))
      ⊜ (Κ (+ 64 / 1) ⊗ ((wi ⊕ (Κ (+ 30 / 1) ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr)))) ⊕ (Κ (+ 120 / 1) ⊗ ((wr ⊗ ((wr ⊗ wi) ⊕ (wi ⊗ wr))) ⊕ (wi ⊗ ((wr ⊗ wr) ⊖ (wi ⊗ wi)))))))) P.≃-refl wr wi)

module At (q : BishopComplex)
  (nzP : Rec.BishopComplexNonzero (gapMinus q))
  (nzM : Rec.BishopComplexNonzero (gapMinus (negC q)))
  (nz2 : Rec.BishopComplexNonzero (gapSquared q)) where

  a = Rec.reciprocalC (gapMinus q) nzP
  b = Rec.reciprocalC (gapMinus (negC q)) nzM
  c = Rec.reciprocalC (gapSquared q) nz2

  U = X q nzP
  V = X (negC q) nzM
  W = X (q *C q) nz2

  plusCancels : (gapPlus q *C b) ≈C A.oneC
  plusCancels = complexTrans
    (A.mulCCongruent (complexSym (gapMinusNeg q)) (C.≈C-refl b))
    (Rec.multiplyReciprocal (gapMinus (negC q)) nzM)

  aRead : a ≈C (gapPlus q *C c)
  aRead = G.reciprocalUnique (gapMinus q) nzP (gapPlus q *C c)
    (complexTrans (complexSym (L.complexMultiplyAssociative (gapMinus q) (gapPlus q) c))
      (complexTrans (A.mulCCongruent (gapFactor q) (C.≈C-refl c))
        (Rec.multiplyReciprocal (gapSquared q) nz2)))

  bRead : b ≈C (gapMinus q *C c)
  bRead = G.reciprocalUnique (gapMinus (negC q)) nzM (gapMinus q *C c)
    (complexTrans (A.mulCCongruent (gapMinusNeg q) (C.≈C-refl _))
      (complexTrans (complexSym (L.complexMultiplyAssociative (gapPlus q) (gapMinus q) c))
        (complexTrans (A.mulCCongruent
          (complexTrans (L.complexMultiplyCommutative (gapPlus q) (gapMinus q)) (gapFactor q))
          (C.≈C-refl c)) (Rec.multiplyReciprocal (gapSquared q) nz2))))

  abRead : (a *C b) ≈C c
  abRead = complexSym (G.reciprocalUnique (gapSquared q) nz2 (a *C b)
    (complexTrans (inversePairReassociate q a b)
      (complexTrans (A.mulCCongruent (Rec.multiplyReciprocal (gapMinus q) nzP) plusCancels)
        (L.complexMultiplyLeftIdentity A.oneC))))

  sumX : (U +C V) ≈C scale 4 W
  sumX = complexTrans
    (A.addCCongruent
      (A.mulCCongruent (C.≈C-refl q) (A.mulCCongruent aRead aRead))
      (A.mulCCongruent (C.≈C-refl (negC q)) (A.mulCCongruent bRead bRead)))
    (sumWithCommonInverse q c)

  productX : (U *C V) ≈C negC W
  productX = complexTrans (productReassociate q a b)
    (negCong (A.mulCCongruent (C.≈C-refl (q *C q)) (A.mulCCongruent abRead abRead)))

  sym4Cong : ∀ {s s' p p'} → s ≈C s' → p ≈C p' → sym4 s p ≈C sym4 s' p'
  sym4Cong s p = A.addCCongruent s
    (scaleCong 6 (A.subCCongruent (A.mulCCongruent s s) (scaleCong 2 p)))

  sym6Cong : ∀ {s s' p p'} → s ≈C s' → p ≈C p' → sym6 s p ≈C sym6 s' p'
  sym6Cong s p = A.addCCongruent
    (A.addCCongruent s (scaleCong 30 (A.subCCongruent (A.mulCCongruent s s) (scaleCong 2 p))))
    (scaleCong 120 (A.subCCongruent (A.mulCCongruent s (A.mulCCongruent s s))
      (scaleCong 3 (A.mulCCongruent p s))))

  -- Both identities preserve the negative half-sheet, including q=0.
  distribution4 : (P4 U +C P4 V) ≈C scale 16 (P4 W)
  distribution4 = complexTrans (symmetric4 U V)
    (complexTrans (sym4Cong sumX productX) (scaled4 W))

  distribution6 : (P6 U +C P6 V) ≈C scale 64 (P6 W)
  distribution6 = complexTrans (symmetric6 U V)
    (complexTrans (sym6Cong sumX productX) (scaled6 W))
