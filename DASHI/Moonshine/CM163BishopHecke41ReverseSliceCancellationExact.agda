module DASHI.Moonshine.CM163BishopHecke41ReverseSliceCancellationExact where

-- Source-written, kernel pending. Cancel the geometric double
-- collision only at an apart test coordinate; no inverse j chart.
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product.Base using (_,_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHecke41RestSlopeLimitExact as Slope
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as PS
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open import Agda.Builtin.Nat using (Nat)
import Real as R
open R using (_⋆)
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

centerDifference : ∀ w → ((Shift.K +C w) -C Shift.K) ≈C w
centerDifference w =
  (let open P.ℝ-Solver in solve 2 (λ k x → (k ⊕ x) ⊖ k ⊜ x)
    P.≃-refl (C.re Shift.K) (C.re w)) ,
  (let open P.ℝ-Solver in solve 2 (λ k x → (k ⊕ x) ⊖ k ⊜ x)
    P.≃-refl (C.im Shift.K) (C.im w))

restCong : ∀ {n} (c : Fin n → BishopComplex) {x y} →
  x ≈C y → Cross.rest c x ≈C Cross.rest c y
restCong c h = Prod.productCong _ _ (λ i → A.addCCongruent (C.≈C-refl _) h)

packetFactor : ∀ w → Poly.poly (Shift.K +C w) Packet.slice ≈C
  (powC w 2 *C Shift.sComplement w)
packetFactor w = complexTrans (complexSym (Shift.literalShift w Packet.slice))
  (Shift.doubleZero w (PS.shift Packet.slice) PS.sZero PS.sLinearZero)

module At (inputs : Round11.BishopCutset) where
  module H = Cross.At inputs
  module S = Slope.At inputs

  -- The two fixed-chart values are K once the selected CM root is
  -- attached. The remaining input is the actual reverse polynomial
  -- identity, not a fabricated equality of the forty-factor tails.
  productFactor : ∀ w →
    H.chart Fixed.p Fin.zero ≈C Shift.K →
    H.chart Fixed.p (Fin.suc Fin.zero) ≈C Shift.K →
    H.G.product Fixed.p (Shift.K +C w) ≈C
      (powC w 2 *C Cross.rest (H.c Fixed.p) w)
  productFactor w h0 h1 =
    let y = Shift.K +C w
        r = Cross.rest (H.c Fixed.p) w
        d0 = complexTrans (A.subCCongruent (C.≈C-refl _) h0) (centerDifference w)
        d1 = complexTrans (A.subCCongruent (C.≈C-refl _) h1) (centerDifference w)
        tail = complexTrans (H.tailAt Fixed.p y)
          (restCong (H.c Fixed.p) (centerDifference w))
    in complexTrans (A.mulCCongruent d0 (A.mulCCongruent d1 tail))
      (complexTrans (complexSym (L.complexMultiplyAssociative w w r))
        (A.mulCCongruent (Power.powTwo w) (C.≈C-refl _)))

  reverseSlice : ∀ w →
    Rec.BishopComplexNonzero w →
    H.chart Fixed.p Fin.zero ≈C Shift.K →
    H.chart Fixed.p (Fin.suc Fin.zero) ≈C Shift.K →
    H.G.product Fixed.p (Shift.K +C w) ≈C Poly.poly (Shift.K +C w) Packet.slice →
    Cross.rest (H.c Fixed.p) w ≈C Shift.sComplement w
  reverseSlice w nz h0 h1 identity =
    J.cancelLeft (powC w 2) _ _ (J.nonzeroPower nz 2)
      (complexTrans (complexSym (productFactor w h0 h1))
        (complexTrans identity (packetFactor w)))

  centerSlope : (w : Nat → BishopComplex) →
    (∀ n → Rec.BishopComplexNonzero (w n)) → Lim.Conv w A.zeroC →
    H.chart Fixed.p Fin.zero ≈C Shift.K →
    H.chart Fixed.p (Fin.suc Fin.zero) ≈C Shift.K →
    (∀ n → H.G.product Fixed.p (Shift.K +C w n) ≈C
      Poly.poly (Shift.K +C w n) Packet.slice) →
    Cross.slope (H.c Fixed.p) A.zeroC ≈C Poly.realC (PS.s3 ⋆)
  centerSlope w nz cv h0 h1 identity =
    S.centerSlopeFromReverseSlice w nz cv
      (λ n → reverseSlice (w n) (nz n) h0 h1 (identity n))
