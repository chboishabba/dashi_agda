module DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact where

-- Source-written, kernel pending. The actual 42 affine charts and the
-- recovered exact S/T correction words now have literal Bishop readouts.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopDiskSetoidTransportExact as Cong
import DASHI.Moonshine.CM163ClassicalHecke41LatticeSpecializationExact as B
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Moonshine.CM163Hecke41CorrectionWordsExact as W
import DASHI.Moonshine.CM163BishopHecke41ProjectiveRowsExact as Rw
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_)
open Comp using (complexTrans; complexSym)
open Rw using (Read; read)

inv41 fortyOne : ℝ
inv41 = (+ 1 / 41) ⋆
fortyOne = (+ 41 / 1) ⋆

invPositive : R._<_ R.0ℝ inv41
invPositive = P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / 41) (QP.positive⁻¹ (+ 1 / 41))

pPositive : R._<_ R.0ℝ fortyOne
pPositive = P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 41 / 1) (QP.positive⁻¹ (+ 41 / 1))

real41 : BishopComplex
real41 = C.complex fortyOne R.0ℝ

real41NZ : Rec.BishopComplexNonzero real41
real41NZ = NZ.complexNonzeroFromRealApart (inj₂ pPositive)

finitePoint : Nat → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
finitePoint k p = U.bishop-upper-half-plane-point
  (C.complex (inv41 * (C.re (U.tau p) + K.embedInteger (+ k))) (inv41 * C.im (U.tau p)))
  (J.positiveMul invPositive (U.imaginaryPositive p))

infinityPoint : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
infinityPoint p = U.bishop-upper-half-plane-point (A.scaleC fortyOne (U.tau p))
  (J.positiveMul pPositive (U.imaginaryPositive p))

chartPoint : Fin 42 → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
chartPoint i p with toℕ i ≟ 41
... | yes _ = infinityPoint p
... | no _ = finitePoint (toℕ i) p

finiteRows : Nat → B.Rows
finiteRows k = B.rows (L.lattice-point (+ 1) (+ k)) (L.lattice-point (+ 0) (+ 41))

infinityRows : B.Rows
infinityRows = B.rows (L.lattice-point (+ 41) (+ 0)) (L.lattice-point (+ 0) (+ 1))

finiteShape : ∀ k → B.finiteImage k H.identityRows ≡ finiteRows k
finiteShape k = cong₂ B.rows
  (L.lattice-ext
    (let open +-*-Solver in solve 1 (λ k → Κ (+ 1) :+ k :* Κ (+ 0) := Κ (+ 1)) refl (+ k))
    (let open +-*-Solver in solve 1 (λ k → Κ (+ 0) :+ k :* Κ (+ 1) := k) refl (+ k)))
  refl

finiteRead : ∀ k p → Read (finiteRows k) p (finitePoint k p)
finiteRead k p = read real41 real41NZ
  ((let open P.ℝ-Solver in solve 3 (λ x y k →
     Κ 1ℚᵘ ⊗ x ⊕ k ⊜ Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ (x ⊕ k)) ⊖ Κ 0ℚᵘ ⊗ (Κ (+ 1 / 41) ⊗ y))
     P.≃-refl (C.re (U.tau p)) (C.im (U.tau p)) (K.embedInteger (+ k))) ,
   (let open P.ℝ-Solver in solve 3 (λ x y k →
     Κ 1ℚᵘ ⊗ y ⊜ Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ y) ⊕ Κ 0ℚᵘ ⊗ (Κ (+ 1 / 41) ⊗ (x ⊕ k)))
     P.≃-refl (C.re (U.tau p)) (C.im (U.tau p)) (K.embedInteger (+ k))))
  ((let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊕ Κ (+ 41 / 1) ⊜ Κ (+ 41 / 1)) P.≃-refl (C.re (U.tau p))) ,
   (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊗ y ⊜ Κ 0ℚᵘ) P.≃-refl (C.im (U.tau p))))

infinityRead : ∀ p → Read infinityRows p (infinityPoint p)
infinityRead p = read A.oneC J.nonzeroOne
  (complexTrans (P.+-identityʳ _ , P.≃-refl)
    (complexSym (Laws.complexMultiplyLeftIdentity _)))
  (Rw.oneRow (U.tau p))

chartRead : ∀ i p → Read (H.chart i) p (chartPoint i p)
chartRead i p with toℕ i ≟ 41
... | yes _ = infinityRead p
... | no _ = subst (λ r → Read r p (finitePoint (toℕ i) p)) (sym (finiteShape (toℕ i))) (finiteRead (toℕ i) p)

-- Literal row multiplication is the same left/right action already
-- used by the original 84 generator-edge certificates.
matrixShape : ∀ g → H.left g H.identityRows ≡
  B.rows (L.lattice-point (L.a g) (L.b g)) (L.lattice-point (L.c g) (L.d g))
matrixShape g = cong₂ B.rows (row (L.a g) (L.b g)) (row (L.c g) (L.d g))
  where
  row : ∀ a b → B.add (B.scale a (B.first H.identityRows)) (B.scale b (B.second H.identityRows)) ≡ L.lattice-point a b
  row a b = L.lattice-ext
    (let open +-*-Solver in solve 2 (λ a b → a :* Κ (+ 1) :+ b :* Κ (+ 0) := a) refl a b)
    (let open +-*-Solver in solve 2 (λ a b → a :* Κ (+ 0) :+ b :* Κ (+ 1) := b) refl a b)

leftMul : ∀ g r → H.mul (H.left g H.identityRows) r ≡ H.left g r
leftMul g r = cong (λ m → H.mul m r) (matrixShape g)

rightMul : ∀ r g → H.mul r (H.left g H.identityRows) ≡ H.right r g
rightMul (B.rows (L.lattice-point a b) (L.lattice-point c d)) g =
  cong (H.mul (B.rows (L.lattice-point a b) (L.lattice-point c d))) (matrixShape g)

sMatrix : ∀ i → H.mul (H.chart i) (W.stepRows W.s) ≡
  H.mul (W.matrix (W.sWord i)) (H.chart (H.sIndex i))
sMatrix i = trans (rightMul (H.chart i) H.S)
  (trans (H.sEdge i) (trans (sym (leftMul (H.sCorrection i) (H.chart (H.sIndex i))))
    (cong (λ m → H.mul m (H.chart (H.sIndex i))) (sym (W.sWordRead i)))))

tMatrix : ∀ i → H.mul (H.chart i) (W.stepRows W.t) ≡
  H.mul (W.matrix (W.tWord i)) (H.chart (H.tIndex i))
tMatrix i = trans (rightMul (H.chart i) H.T)
  (trans (H.tEdge i) (trans (sym (leftMul (H.tCorrection i) (H.chart (H.tIndex i))))
    (cong (λ m → H.mul m (H.chart (H.tIndex i))) (sym (W.tWordRead i)))))

sPoint : ∀ i p → U.tau (chartPoint i (G.actS p)) ≈C
  U.tau (Rw.word (W.sWord i) (chartPoint (H.sIndex i) p))
sPoint i p =
  let q = chartPoint i (G.actS p)
      v = chartPoint (H.sIndex i) p
      u = Rw.word (W.sWord i) v
      r = H.mul (W.matrix (W.sWord i)) (H.chart (H.sIndex i))
      first = Rw.compose (H.chart i) (W.stepRows W.s) p (G.actS p) q
        (Rw.stepRead W.s p) (chartRead i (G.actS p))
      second = Rw.compose (W.matrix (W.sWord i)) (H.chart (H.sIndex i)) p v u
        (chartRead (H.sIndex i) p) (Rw.wordRead (W.sWord i) v)
  in Rw.samePoint r p q u (subst (λ m → Read m p q) (sMatrix i) first) second

tPoint : ∀ i p → U.tau (chartPoint i (G.actT p)) ≈C
  U.tau (Rw.word (W.tWord i) (chartPoint (H.tIndex i) p))
tPoint i p =
  let q = chartPoint i (G.actT p)
      v = chartPoint (H.tIndex i) p
      u = Rw.word (W.tWord i) v
      r = H.mul (W.matrix (W.tWord i)) (H.chart (H.tIndex i))
      first = Rw.compose (H.chart i) (W.stepRows W.t) p (G.actT p) q
        (Rw.stepRead W.t p) (chartRead i (G.actT p))
      second = Rw.compose (W.matrix (W.tWord i)) (H.chart (H.tIndex i)) p v u
        (chartRead (H.tIndex i) p) (Rw.wordRead (W.tWord i) v)
  in Rw.samePoint r p q u (subst (λ m → Read m p q) (tMatrix i) first) second

module At (inputs : Round11.BishopCutset) where
  module KJ = J.At inputs
  module E = Cong.At inputs

  stepGuard : ∀ g p → KJ.Guard p → KJ.Guard (Rw.step g p)
  stepGuard W.s = KJ.guardS
  stepGuard W.t = KJ.guardT

  stepJ : ∀ g p (a : KJ.Guard p) (b : KJ.Guard (Rw.step g p)) →
    KJ.j (Rw.step g p) b ≈C KJ.j p a
  stepJ W.s = KJ.jS
  stepJ W.t = KJ.jT

  wordGuard : ∀ w p → KJ.Guard p → KJ.Guard (Rw.word w p)
  wordGuard [] p nz = nz
  wordGuard (g ∷ gs) p nz = stepGuard g (Rw.word gs p) (wordGuard gs p nz)

  wordJ : ∀ w p (a : KJ.Guard p) (b : KJ.Guard (Rw.word w p)) →
    KJ.j (Rw.word w p) b ≈C KJ.j p a
  wordJ [] p a b = E.jCong p p (C.≈C-refl _) b a
  wordJ (g ∷ gs) p a b = complexTrans (stepJ g (Rw.word gs p) (wordGuard gs p a) b)
    (wordJ gs p a (wordGuard gs p a))

  sGuard : ∀ i p → KJ.Guard (chartPoint (H.sIndex i) p) → KJ.Guard (chartPoint i (G.actS p))
  sGuard i p nz = E.guardCong _ _ (complexSym (sPoint i p)) (wordGuard (W.sWord i) _ nz)

  tGuard : ∀ i p → KJ.Guard (chartPoint (H.tIndex i) p) → KJ.Guard (chartPoint i (G.actT p))
  tGuard i p nz = E.guardCong _ _ (complexSym (tPoint i p)) (wordGuard (W.tWord i) _ nz)

  sChartJ : ∀ i p (a : KJ.Guard (chartPoint (H.sIndex i) p))
    (b : KJ.Guard (chartPoint i (G.actS p))) →
    KJ.j (chartPoint i (G.actS p)) b ≈C KJ.j (chartPoint (H.sIndex i) p) a
  sChartJ i p a b = complexTrans (E.jCong _ _ (sPoint i p) b (wordGuard (W.sWord i) _ a))
    (wordJ (W.sWord i) _ a (wordGuard (W.sWord i) _ a))

  tChartJ : ∀ i p (a : KJ.Guard (chartPoint (H.tIndex i) p))
    (b : KJ.Guard (chartPoint i (G.actT p))) →
    KJ.j (chartPoint i (G.actT p)) b ≈C KJ.j (chartPoint (H.tIndex i) p) a
  tChartJ i p a b = complexTrans (E.jCong _ _ (tPoint i p) b (wordGuard (W.tWord i) _ a))
    (wordJ (W.tWord i) _ a (wordGuard (W.tWord i) _ a))
