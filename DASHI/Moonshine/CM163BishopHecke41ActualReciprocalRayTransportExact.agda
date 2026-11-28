module DASHI.Moonshine.CM163BishopHecke41ActualReciprocalRayTransportExact where

-- R2, SOURCE-WRITTEN / KERNEL PENDING.
-- Actual modular words S A1 and T^-1 S A0 on the original Fin42
-- chart family. Cancel only certified nonzero denominators.
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base as Fin
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₂)
import Real as R
import RealProperties as P
open R using (_+_; _-_; _*_; _⋆)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.CM163BishopHecke41ReciprocalRayCoordinateExact as Ray
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaNonvanishingExact as Global
import DASHI.Moonshine.JInvariantBishopDiskSetoidTransportExact as Cong
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

minusT : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
minusT p = U.bishop-upper-half-plane-point
  (C.complex (C.re (U.tau p) - R.1ℝ) (C.im (U.tau p))) (U.imaginaryPositive p)

undoT : ∀ p → U.tau (Gen.actT (minusT p)) ≈C U.tau p
undoT p =
  (let open P.ℝ-Solver in solve 1 (λ x → (x ⊖ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ ⊜ x)
    P.≃-refl (C.re (U.tau p))) , P.≃-refl

minusTRead : ∀ p → U.tau (minusT p) ≈C (U.tau p -C A.oneC)
minusTRead p = P.≃-refl ,
  (let open P.ℝ-Solver in solve 1 (λ y → y ⊜ y ⊖ Κ 0ℚᵘ)
    P.≃-refl (C.im (U.tau p)))

forward reverse : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
forward p = Gen.actS (Chart.finitePoint 1 p)
reverse p = minusT (Gen.actS (Chart.finitePoint 0 p))

den1Read : ∀ p → scaleC Chart.fortyOne (U.tau (Chart.finitePoint 1 p)) ≈C Geo.fDen (U.tau p)
den1Read p =
  (let open P.ℝ-Solver in solve 1 (λ x →
    Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ (x ⊕ Κ 1ℚᵘ)) ⊜ x ⊕ Κ 1ℚᵘ)
    P.≃-refl (C.re (U.tau p))) ,
  (let open P.ℝ-Solver in solve 1 (λ y →
    Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ y) ⊜ y ⊕ Κ 0ℚᵘ)
    P.≃-refl (C.im (U.tau p)))

den0Read : ∀ p → scaleC Chart.fortyOne (U.tau (Chart.finitePoint 0 p)) ≈C U.tau p
den0Read p =
  (let open P.ℝ-Solver in solve 1 (λ x →
    Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ (x ⊕ Κ 0ℚᵘ)) ⊜ x)
    P.≃-refl (C.re (U.tau p))) ,
  (let open P.ℝ-Solver in solve 1 (λ y →
    Κ (+ 41 / 1) ⊗ (Κ (+ 1 / 41) ⊗ y) ⊜ y)
    P.≃-refl (C.im (U.tau p)))

scaledMinus : scaleC Chart.fortyOne Gen.minusOneC ≈C Geo.fNum Geo.tau
scaledMinus =
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 41 / 1) ⊗ (⊝ Κ 1ℚᵘ) ⊜ Κ ((- (+ 41)) / 1)) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 41 / 1) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl)

scaleLeft : ∀ h a b → (scaleC h a *C b) ≈C scaleC h (a *C b)
scaleLeft h a b =
  complexTrans (L.complexMultiplyCommutative (scaleC h a) b)
    (complexTrans (Fixed.scaleRight h b a)
      (A.scaleCCongruent (L.complexMultiplyCommutative b a) h))

forwardClear : ∀ p → (Geo.fDen (U.tau p) *C U.tau (forward p)) ≈C Geo.fNum (U.tau p)
forwardClear p = complexTrans (A.mulCCongruent (complexSym (den1Read p)) (C.≈C-refl _))
  (complexTrans (scaleLeft Chart.fortyOne _ _)
    (complexTrans (A.scaleCCongruent (Gen.tauTimesS (Chart.finitePoint 1 p)) Chart.fortyOne)
      scaledMinus))

reverseS : ∀ p → (U.tau p *C U.tau (Gen.actS (Chart.finitePoint 0 p))) ≈C Geo.fNum (U.tau p)
reverseS p = complexTrans (A.mulCCongruent (complexSym (den0Read p)) (C.≈C-refl _))
  (complexTrans (scaleLeft Chart.fortyOne _ _)
    (complexTrans (A.scaleCCongruent (Gen.tauTimesS (Chart.finitePoint 0 p)) Chart.fortyOne)
      scaledMinus))

reverseClear : ∀ p → (Geo.gDen (U.tau p) *C U.tau (reverse p)) ≈C Geo.gNum (U.tau p)
reverseClear p = complexTrans (A.mulCCongruent (C.≈C-refl _) (minusTRead _))
  (complexTrans (Alg.mulSub (U.tau p) _ A.oneC)
    (A.subCCongruent (reverseS p) (L.complexMultiplyRightIdentity _)))

fDenNZ : ∀ p → Rec.BishopComplexNonzero (Geo.fDen (U.tau p))
fDenNZ p = NZ.complexNonzeroFromImagApart
  (NZ.apartCongruent (P.≃-symm (P.+-identityʳ (C.im (U.tau p))))
    (inj₂ (U.imaginaryPositive p)))

diskNZ : ∀ n → Rec.BishopComplexNonzero (U.tau (Ray.ray n) -C Geo.tauBar)
diskNZ n = Phase.guardCong (complexSym (Ray.diskDenRead n))
  (Cancel.nonzeroMul Ray.dNZ (Ray.denNZ n))

-- Algebra for a cleared cross ratio. These are rearrangements, not
-- numerical root tests or inversions of the perturbation.
swapMiddle : ∀ a b c → (a *C (b *C c)) ≈C (b *C (a *C c))
swapMiddle a b c = complexTrans (complexSym (L.complexMultiplyAssociative a b c))
  (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative a b) (C.≈C-refl _))
    (L.complexMultiplyAssociative b a c))

moveLast : ∀ a b c → (a *C (b *C c)) ≈C (c *C (a *C b))
moveLast a b c = complexTrans (complexSym (L.complexMultiplyAssociative a b c))
  (L.complexMultiplyCommutative (a *C b) c)

clearShift : ∀ D N v t → (D *C v) ≈C N →
  (D *C (v -C t)) ≈C (N -C t *C D)
clearShift D N v t h = complexTrans (Alg.mulSub D v t)
  (A.subCCongruent h (L.complexMultiplyCommutative D t))

rotate : ∀ z v D N k w →
  Rec.BishopComplexNonzero D →
  Rec.BishopComplexNonzero (z -C Geo.tauBar) →
  (D *C v) ≈C N →
  (z -C Geo.tau) ≈C (w *C (z -C Geo.tauBar)) →
  ((N -C Geo.tau *C D) *C (z -C Geo.tauBar)) ≈C
    (k *C ((N -C Geo.tauBar *C D) *C (z -C Geo.tau))) →
  (v -C Geo.tau) ≈C ((k *C w) *C (v -C Geo.tauBar))
rotate z v D N k w dn zn clear disk rotation =
  let H = z -C Geo.tauBar
      A0 = N -C Geo.tau *C D
      B0 = N -C Geo.tauBar *C D
      rightRead = complexTrans
        (A.mulCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) disk))
        (complexTrans (A.mulCCongruent (C.≈C-refl _) (swapMiddle B0 w H))
          (complexTrans (A.mulCCongruent (C.≈C-refl _) (moveLast w B0 H))
            (complexTrans (swapMiddle k H (w *C B0))
              (A.mulCCongruent (C.≈C-refl _) (complexSym (L.complexMultiplyAssociative k w B0))))))
      numerator = Cancel.cancelLeft H A0 ((k *C w) *C B0) zn
        (complexTrans (L.complexMultiplyCommutative H A0)
          (complexTrans rotation rightRead))
  in Cancel.cancelLeft D _ _ dn
    (complexTrans (clearShift D N v Geo.tau clear)
      (complexTrans numerator
        (complexTrans (A.mulCCongruent (C.≈C-refl _) (complexSym (clearShift D N v Geo.tauBar clear)))
          (swapMiddle (k *C w) D (v -C Geo.tauBar)))))

forwardDisk : ∀ n →
  (U.tau (forward (Ray.ray n)) -C Geo.tau) ≈C
  ((Geo.alpha *C Ray.w n) *C (U.tau (forward (Ray.ray n)) -C Geo.tauBar))
forwardDisk n =
  let p = Ray.ray n; z = U.tau p
  in rotate z (U.tau (forward p)) (Geo.fDen z) (Geo.fNum z) Geo.alpha (Ray.w n)
    (fDenNZ p) (diskNZ n) (forwardClear p) (Ray.diskRead n)
    (Geo.forwardDiskCleared (C.re z) (C.im z))

reverseDisk : ∀ n →
  (U.tau (reverse (Ray.ray n)) -C Geo.tau) ≈C
  ((Geo.beta *C Ray.w n) *C (U.tau (reverse (Ray.ray n)) -C Geo.tauBar))
reverseDisk n =
  let p = Ray.ray n; z = U.tau p
  in rotate z (U.tau (reverse p)) (Geo.gDen z) (Geo.gNum z) Geo.beta (Ray.w n)
    (Gen.tauNZ p) (diskNZ n) (reverseClear p) (Ray.diskRead n)
    (Geo.reverseDiskCleared (C.re z) (C.im z))

-- The actual branch chart is the modular word, not just a free
-- complex coordinate satisfying the cleared relation.
module At (inputs : Round11.BishopCutset) where
  module G = Global.At inputs
  module E = Cong.At inputs

  jS : ∀ p → G.j (Gen.actS p) ≈C G.j p
  jS p = G.KJ.jS p (G.globalGuard p) (G.globalGuard (Gen.actS p))

  jT : ∀ p → G.j (Gen.actT p) ≈C G.j p
  jT p = G.KJ.jT p (G.globalGuard p) (G.globalGuard (Gen.actT p))

  jMinusT : ∀ p → G.j (minusT p) ≈C G.j p
  jMinusT p = complexTrans (complexSym (jT (minusT p)))
    (E.jCong (Gen.actT (minusT p)) p (undoT p)
      (G.globalGuard _) (G.globalGuard p))

  forwardJ : ∀ p → G.j (forward p) ≈C G.j (Chart.chartPoint (Fin.suc Fin.zero) p)
  forwardJ p = jS (Chart.finitePoint 1 p)

  reverseJ : ∀ p → G.j (reverse p) ≈C G.j (Chart.chartPoint Fin.zero p)
  reverseJ p = complexTrans (jMinusT (Gen.actS (Chart.finitePoint 0 p)))
    (jS (Chart.finitePoint 0 p))
