module DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryFourierExact where

-- Source-written, kernel pending. Approach z=1/2 vertically on the
-- original Machin exponential. The boundary gap is 2, not a disk guard.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact as ExpCont
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Trig
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryTermsExact as H
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; _-C_; scaleC; powC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges)

negativeOne : BishopComplex
negativeOne = C.complex (R.- R.1ℝ) R.0ℝ
halfC : BishopComplex
halfC = C.complex D.half R.0ℝ
negativeQuarter : BishopComplex
negativeQuarter = C.complex ((R.- ((+ 1 / 4) ⋆))) R.0ℝ

gapNZ : Rec.BishopComplexNonzero (Row.gapMinus negativeOne)
gapNZ = NZ.complexNonzeroFromRealApart (inj₂
  (P.<-respʳ-≃
    (let open P.ℝ-Solver in solve 0 (Κ (+ 2 / 1) ⊜ Κ 1ℚᵘ ⊖ (⊝ Κ 1ℚᵘ)) P.≃-refl)
    Radius.twoPositive))

gapHalf : (Row.gapMinus negativeOne *C halfC) ≈C A.oneC
gapHalf =
  (let open P.ℝ-Solver in solve 0
    ((Κ 1ℚᵘ ⊖ (⊝ Κ 1ℚᵘ)) ⊗ Κ (+ 1 / 2) ⊖ (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ) ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 0
    ((Κ 1ℚᵘ ⊖ (⊝ Κ 1ℚᵘ)) ⊗ Κ 0ℚᵘ ⊕ (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ) ⊗ Κ (+ 1 / 2) ⊜ Κ 0ℚᵘ) P.≃-refl)

inverseRead : Rec.reciprocalC (Row.gapMinus negativeOne) gapNZ ≈C halfC
inverseRead = G.reciprocalUnique _ gapNZ halfC gapHalf

xRead : (negativeOne *C (halfC *C halfC)) ≈C negativeQuarter
xRead = 
  (let open P.ℝ-Solver in solve 0
    ((⊝ Κ 1ℚᵘ) ⊗ (Κ (+ 1 / 2) ⊗ Κ (+ 1 / 2) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)
      ⊖ Κ 0ℚᵘ ⊗ (Κ (+ 1 / 2) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ Κ (+ 1 / 2)) ⊜ ⊝ Κ (+ 1 / 4)) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 0
    ((⊝ Κ 1ℚᵘ) ⊗ (Κ (+ 1 / 2) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ Κ (+ 1 / 2))
      ⊕ Κ 0ℚᵘ ⊗ (Κ (+ 1 / 2) ⊗ Κ (+ 1 / 2) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ) P.≃-refl)

module At (inputs : Round11.BishopCutset) where
  module Rows = D.At inputs
  q : Nat → BishopComplex
  q n = Rows.q (H.point n)
  a : Nat → ℝ
  a n = R.- ((D.two * D.pi) * Chart.h n)

  aNull : Seq._ConvergesTo_ a R.0ℝ
  aNull = Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.-xₙ→-x₀ (_ , Inv.mulR (Power.constantConverges (D.two * D.pi)) Leaf.hNull))
    (let open P.ℝ-Solver in solve 1
      (λ a → ⊝ (a ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ) P.≃-refl (D.two * D.pi))

  radialConv : Seq._ConvergesTo_ (λ n → Exp.bishopExp (a n)) R.1ℝ
  radialConv = Seq.xₙ→x∧x≃y⇒xₙ→y
    (ExpCont.originalBishopExpSequentiallyContinuous a R.0ℝ aNull) ExpZero.bishopExpZero

  angleRead : (D.two * D.pi) * D.half ≃ D.pi
  angleRead = let open P.ℝ-Solver in solve 1
    (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ Κ (+ 1 / 2) ⊜ p) P.≃-refl D.pi

  qRead : ∀ n → q n ≈C C.complex (R.- (Exp.bishopExp (a n))) R.0ℝ
  qRead n =
    P.≃-trans (P.*-congˡ (P.≃-trans
      (Trig.bishopCosCongruent (Round11.concreteTermIdentification inputs) angleRead) (proj₂ Rows.endpoints)))
      (let open P.ℝ-Solver in solve 1 (λ r → r ⊗ (⊝ Κ 1ℚᵘ) ⊜ ⊝ r) P.≃-refl (Exp.bishopExp (a n))) ,
    P.≃-trans (P.*-congˡ (P.≃-trans
      (Trig.bishopSinCongruent (Round11.concreteTermIdentification inputs) angleRead) (proj₁ Rows.endpoints)))
      (let open P.ℝ-Solver in solve 1 (λ r → r ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl (Exp.bishopExp (a n)))

  qConv : Lim.Conv q negativeOne
  qConv = Lim.convTransport (λ n → complexSym (qRead n))
    (original-bishop-pointwise-complex-converges
      (Seq.-xₙ→-x₀ (R.1ℝ , radialConv)) (Power.constantConverges R.0ℝ))

  gap : Nat → BishopComplex
  gap n = Row.gapMinus (q n)
  iv : Nat → BishopComplex
  iv n = Rec.reciprocalC (gap n) (Rows.gapNZ (H.point n))

  ivConv : Lim.Conv iv halfC
  ivConv = Lim.limitTransport inverseRead
    (Inv.inverseLimit gapNZ (Lim.subConv (Lim.constantC A.oneC) qConv)
      (λ n → Rec.multiplyReciprocal (gap n) (Rows.gapNZ (H.point n))))

  XConv : Lim.Conv (λ n → Row.X (q n) (Rows.gapNZ (H.point n))) negativeQuarter
  XConv = Lim.limitTransport xRead (Inv.mulConv qConv (Inv.mulConv ivConv ivConv))

  F4Conv : Lim.Conv (λ n → Rows.row4 (H.point n)) (Row.P4 negativeQuarter)
  F4Conv = Lim.addConv XConv
    (Inv.scaleConv (Power.constantConverges ((+ 6 / 1) ⋆)) (Inv.mulConv XConv XConv))

  F6Conv : Lim.Conv (λ n → Rows.row6 (H.point n)) (Row.P6 negativeQuarter)
  F6Conv = Lim.addConv
    (Lim.addConv XConv (Inv.scaleConv (Power.constantConverges ((+ 30 / 1) ⋆)) (Inv.mulConv XConv XConv)))
    (Inv.scaleConv (Power.constantConverges ((+ 120 / 1) ⋆)) (Inv.mulConv XConv (Inv.mulConv XConv XConv)))
