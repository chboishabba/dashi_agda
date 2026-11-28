module DASHI.Moonshine.CM163BishopHecke41RestSlopeLimitExact where

-- SOURCE-WRITTEN, kernel pending. Native continuity of the actual
-- finite forty-factor slope, and reverse-slice center-coefficient
-- extraction. No differentiability of the forty factors required.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Unnormalised using (ℚᵘ)
open import Data.Product.Base using (_,_)
import Real as R
open R using (_⋆)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Packet
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)

restContinuous : ∀ {n} (c : Nat → Fin n → BishopComplex) (d : Fin n → BishopComplex)
  {x : Nat → BishopComplex} {z} →
  (∀ i → Lim.Conv (λ k → c k i) (d i)) → Lim.Conv x z →
  Lim.Conv (λ k → Cross.rest (c k) (x k)) (Cross.rest d z)
restContinuous {zero} c d hc hx = Lim.constantC A.oneC
restContinuous {suc n} c d hc hx = Conv.mulConv (Lim.addConv (hc Fin.zero) hx)
  (restContinuous (λ k i → c k (Fin.suc i)) (λ i → d (Fin.suc i)) (λ i → hc (Fin.suc i)) hx)

slopeContinuous : ∀ {n} (c : Nat → Fin n → BishopComplex) (d : Fin n → BishopComplex)
  {x : Nat → BishopComplex} {z} →
  (∀ i → Lim.Conv (λ k → c k i) (d i)) → Lim.Conv x z →
  Lim.Conv (λ k → Cross.slope (c k) (x k)) (Cross.slope d z)
slopeContinuous {zero} c d hc hx = Lim.constantC A.zeroC
slopeContinuous {suc n} c d hc hx =
  Lim.addConv (restContinuous (λ k i → c k (Fin.suc i)) (λ i → d (Fin.suc i)) (λ i → hc (Fin.suc i)) hx)
    (Conv.mulConv (hc Fin.zero)
      (slopeContinuous (λ k i → c k (Fin.suc i)) (λ i → d (Fin.suc i)) (λ i → hc (Fin.suc i)) hx))

restJet : ∀ {n} (c : Fin n → BishopComplex) (w : Nat → BishopComplex) →
  Lim.Conv w A.zeroC →
  J.Jet w (λ k → Cross.rest c (w k)) (Prod.product c) (Cross.slope c A.zeroC)
restJet c w cv = record
  { J.quotient = λ k → Cross.slope c (w k)
  ; J.factor = λ k → Cross.restDifference c (w k)
  ; J.limit = slopeContinuous (λ _ → c) c (λ i → Lim.constantC (c i)) cv }

-- A reverse-slice equality along ANY nonzero null test sequence
-- is enough to identify the center slope. No inverse j chart is
-- required by the coefficient extraction itself.
centerFromSamples : ∀ {n} (c : Fin n → BishopComplex) (cs : List ℚᵘ)
  (w : Nat → BishopComplex) →
  (∀ k → Rec.BishopComplexNonzero (w k)) → Lim.Conv w A.zeroC →
  (∀ k → Cross.rest c (w k) ≈C Shift.asc (w k) cs) →
  Cross.slope c A.zeroC ≈C Poly.realC (Packet.head (Packet.tail cs) ⋆)
centerFromSamples c cs w nz cv eq =
  complexTrans (J.unique nz cv eq (restJet c w cv) (J.ascJet cs cv (J.coordinate w)))
    (L.complexMultiplyLeftIdentity _)

module At (inputs : Round11.BishopCutset) where
  module H = Cross.At inputs

  actualSlopeLimit :
    (p : Nat → U.BishopUpperHalfPlanePoint) →
    (∀ i → Lim.Conv (λ k → H.chart (p k) i) (H.chart Fixed.p i)) →
    Lim.Conv (λ k → H.x (p k)) A.zeroC →
    Lim.Conv (λ k → Cross.slope (H.c (p k)) (H.x (p k))) (Cross.slope (H.c Fixed.p) A.zeroC)
  actualSlopeLimit p charts hx = slopeContinuous (λ k → H.c (p k)) (H.c Fixed.p)
    (λ i → Lim.subConv (Lim.constantC Shift.K) (charts (Fin.suc (Fin.suc i)))) hx

  centerSlopeFromReverseSlice :
    (w : Nat → BishopComplex) → (∀ k → Rec.BishopComplexNonzero (w k)) →
    Lim.Conv w A.zeroC →
    (∀ k → Cross.rest (H.c Fixed.p) (w k) ≈C Shift.sComplement (w k)) →
    Cross.slope (H.c Fixed.p) A.zeroC ≈C Poly.realC (Packet.s3 ⋆)
  centerSlopeFromReverseSlice w nz cv eq =
    centerFromSamples (H.c Fixed.p) (Packet.drop 2 Packet.Sshift) w nz cv eq

  actualSlopeFromReverseSlice :
    (p : Nat → U.BishopUpperHalfPlanePoint) →
    (∀ i → Lim.Conv (λ k → H.chart (p k) i) (H.chart Fixed.p i)) →
    Lim.Conv (λ k → H.x (p k)) A.zeroC →
    (w : Nat → BishopComplex) → (∀ k → Rec.BishopComplexNonzero (w k)) →
    Lim.Conv w A.zeroC →
    (∀ k → Cross.rest (H.c Fixed.p) (w k) ≈C Shift.sComplement (w k)) →
    Lim.Conv (λ k → Cross.slope (H.c (p k)) (H.x (p k))) (Poly.realC (Packet.s3 ⋆))
  actualSlopeFromReverseSlice p charts hx w nz cv eq =
    Lim.limitTransport (centerSlopeFromReverseSlice w nz cv eq) (actualSlopeLimit p charts hx)
