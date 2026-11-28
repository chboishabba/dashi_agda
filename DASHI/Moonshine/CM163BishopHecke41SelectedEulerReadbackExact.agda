module DASHI.Moonshine.CM163BishopHecke41SelectedEulerReadbackExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Identify the two analytic Euler coefficients with the previously
-- constructed signed quotient coefficients on the ORIGINAL selected
-- CM disk.  No CM-root premise, numerical equality or inverse j.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_+_; _*_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as Ring
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as Unit
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as Weight
import DASHI.Moonshine.JInvariantBishopCM163LiteralBracketExact as Br
import DASHI.Moonshine.JInvariantBishopCM163QuotientJetExact as QJ
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Literal
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHecke41ActualJLogPhaseJetExact as Log
import DASHI.Moonshine.CM163BishopHecke41AffineQuotientJetExact as Divide
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as Root
import DASHI.Moonshine.CM163BishopHecke41ActualReciprocalRayTransportExact as Transport
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41EulerMomentEvaluationExact as M
import DASHI.Moonshine.CM163BishopHecke41NormalizedEulerFlowExact as Flow
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact as T
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC; powC)
open Poly using (realC)
open Comp using (complexTrans; complexSym)
open Ring using (_⊕s_; _⊖s_; _⊗s_; _≈s_)


unscale2 : ∀ q v b → ((q *C v) *C ((q *C v) *C b)) ≈C (q *C (q *C (v *C (v *C b))))
unscale2 q v b = (let open P.ℝ-Solver in solve 6 (λ qr qi vr vi br bi →
    ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ br) ⊖ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ bi))) ⊖ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ bi) ⊕ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ br)))) ⊜ ((qr ⊗ ((qr ⊗ ((vr ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))) ⊖ (vi ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))))) ⊖ (qi ⊗ ((vr ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))) ⊕ (vi ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))))))) ⊖ (qi ⊗ ((qr ⊗ ((vr ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))) ⊕ (vi ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))))) ⊕ (qi ⊗ ((vr ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))) ⊖ (vi ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))))))))) P.≃-refl (C.re q) (C.im q) (C.re v) (C.im v) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 6 (λ qr qi vr vi br bi →
    ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ bi) ⊕ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ br))) ⊕ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ ((((qr ⊗ vr) ⊖ (qi ⊗ vi)) ⊗ br) ⊖ (((qr ⊗ vi) ⊕ (qi ⊗ vr)) ⊗ bi)))) ⊜ ((qr ⊗ ((qr ⊗ ((vr ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))) ⊕ (vi ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))))) ⊕ (qi ⊗ ((vr ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))) ⊖ (vi ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))))))) ⊕ (qi ⊗ ((qr ⊗ ((vr ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))) ⊖ (vi ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))))) ⊖ (qi ⊗ ((vr ⊗ ((vr ⊗ bi) ⊕ (vi ⊗ br))) ⊕ (vi ⊗ ((vr ⊗ br) ⊖ (vi ⊗ bi))))))))) P.≃-refl (C.re q) (C.im q) (C.re v) (C.im v) (C.re b) (C.im b))

doubleTaylor : ∀ q x y →
  (((q *C realC ((+ 1 / 2) ⋆)) *C x +C q *C (q *C y)) +C
   ((q *C realC ((+ 1 / 2) ⋆)) *C x +C q *C (q *C y))) ≈C
  ((q *C x) +C ((q *C (q *C y)) +C (q *C (q *C y))))
doubleTaylor q x y = (let open P.ℝ-Solver in solve 6 (λ qr qi xr xi yr yi →
    ((((((qr ⊗ Κ (+ 1 / 2)) ⊖ (qi ⊗ Κ 0ℚᵘ)) ⊗ xr) ⊖ (((qr ⊗ Κ 0ℚᵘ) ⊕ (qi ⊗ Κ (+ 1 / 2))) ⊗ xi)) ⊕ ((qr ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))) ⊖ (qi ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))))) ⊕ (((((qr ⊗ Κ (+ 1 / 2)) ⊖ (qi ⊗ Κ 0ℚᵘ)) ⊗ xr) ⊖ (((qr ⊗ Κ 0ℚᵘ) ⊕ (qi ⊗ Κ (+ 1 / 2))) ⊗ xi)) ⊕ ((qr ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))) ⊖ (qi ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr)))))) ⊜ (((qr ⊗ xr) ⊖ (qi ⊗ xi)) ⊕ (((qr ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))) ⊖ (qi ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr)))) ⊕ ((qr ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))) ⊖ (qi ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re y) (C.im y)) ,
  (let open P.ℝ-Solver in solve 6 (λ qr qi xr xi yr yi →
    ((((((qr ⊗ Κ (+ 1 / 2)) ⊖ (qi ⊗ Κ 0ℚᵘ)) ⊗ xi) ⊕ (((qr ⊗ Κ 0ℚᵘ) ⊕ (qi ⊗ Κ (+ 1 / 2))) ⊗ xr)) ⊕ ((qr ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))) ⊕ (qi ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))))) ⊕ (((((qr ⊗ Κ (+ 1 / 2)) ⊖ (qi ⊗ Κ 0ℚᵘ)) ⊗ xi) ⊕ (((qr ⊗ Κ 0ℚᵘ) ⊕ (qi ⊗ Κ (+ 1 / 2))) ⊗ xr)) ⊕ ((qr ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))) ⊕ (qi ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi)))))) ⊜ (((qr ⊗ xi) ⊕ (qi ⊗ xr)) ⊕ (((qr ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))) ⊕ (qi ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi)))) ⊕ ((qr ⊗ ((qr ⊗ yi) ⊕ (qi ⊗ yr))) ⊕ (qi ⊗ ((qr ⊗ yr) ⊖ (qi ⊗ yi))))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re y) (C.im y))

secondClear : ∀ q x b →
  (q *C ((q *C x) +C ((q *C (b -C x)) +C (q *C (b -C x))))) ≈C
  (((q *C (q *C b)) +C (q *C (q *C b))) -C (q *C (q *C x)))
secondClear q x b = (let open P.ℝ-Solver in solve 6 (λ qr qi xr xi br bi →
    ((qr ⊗ (((qr ⊗ xr) ⊖ (qi ⊗ xi)) ⊕ (((qr ⊗ (br ⊖ xr)) ⊖ (qi ⊗ (bi ⊖ xi))) ⊕ ((qr ⊗ (br ⊖ xr)) ⊖ (qi ⊗ (bi ⊖ xi)))))) ⊖ (qi ⊗ (((qr ⊗ xi) ⊕ (qi ⊗ xr)) ⊕ (((qr ⊗ (bi ⊖ xi)) ⊕ (qi ⊗ (br ⊖ xr))) ⊕ ((qr ⊗ (bi ⊖ xi)) ⊕ (qi ⊗ (br ⊖ xr))))))) ⊜ ((((qr ⊗ ((qr ⊗ br) ⊖ (qi ⊗ bi))) ⊖ (qi ⊗ ((qr ⊗ bi) ⊕ (qi ⊗ br)))) ⊕ ((qr ⊗ ((qr ⊗ br) ⊖ (qi ⊗ bi))) ⊖ (qi ⊗ ((qr ⊗ bi) ⊕ (qi ⊗ br))))) ⊖ ((qr ⊗ ((qr ⊗ xr) ⊖ (qi ⊗ xi))) ⊖ (qi ⊗ ((qr ⊗ xi) ⊕ (qi ⊗ xr)))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 6 (λ qr qi xr xi br bi →
    ((qr ⊗ (((qr ⊗ xi) ⊕ (qi ⊗ xr)) ⊕ (((qr ⊗ (bi ⊖ xi)) ⊕ (qi ⊗ (br ⊖ xr))) ⊕ ((qr ⊗ (bi ⊖ xi)) ⊕ (qi ⊗ (br ⊖ xr)))))) ⊕ (qi ⊗ (((qr ⊗ xr) ⊖ (qi ⊗ xi)) ⊕ (((qr ⊗ (br ⊖ xr)) ⊖ (qi ⊗ (bi ⊖ xi))) ⊕ ((qr ⊗ (br ⊖ xr)) ⊖ (qi ⊗ (bi ⊖ xi))))))) ⊜ ((((qr ⊗ ((qr ⊗ bi) ⊕ (qi ⊗ br))) ⊕ (qi ⊗ ((qr ⊗ br) ⊖ (qi ⊗ bi)))) ⊕ ((qr ⊗ ((qr ⊗ bi) ⊕ (qi ⊗ br))) ⊕ (qi ⊗ ((qr ⊗ br) ⊖ (qi ⊗ bi))))) ⊖ ((qr ⊗ ((qr ⊗ xi) ⊕ (qi ⊗ xr))) ⊕ (qi ⊗ ((qr ⊗ xr) ⊖ (qi ⊗ xi)))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re b) (C.im b))

secondCombine : ∀ x y j → (y -C (x -C j)) ≈C (((x +C y) -C (x +C x)) +C j)
secondCombine x y j = (let open P.ℝ-Solver in solve 6 (λ xr xi yr yi jr ji →
    (yr ⊖ (xr ⊖ jr)) ⊜ (((xr ⊕ yr) ⊖ (xr ⊕ xr)) ⊕ jr)) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y) (C.re j) (C.im j)) ,
  (let open P.ℝ-Solver in solve 6 (λ xr xi yr yi jr ji →
    (yi ⊖ (xi ⊖ ji)) ⊜ (((xi ⊕ yi) ⊖ (xi ⊕ xi)) ⊕ ji)) P.≃-refl (C.re x) (C.im x) (C.re y) (C.im y) (C.re j) (C.im j))

firstGather : ∀ q x y u j → (q *C ((x *C u) +C (y *C j))) ≈C
  ((x *C (q *C u)) +C (y *C (q *C j)))
firstGather q x y u j = (let open P.ℝ-Solver in solve 10 (λ qr qi xr xi yr yi ur ui jr ji →
    ((qr ⊗ (((xr ⊗ ur) ⊖ (xi ⊗ ui)) ⊕ ((yr ⊗ jr) ⊖ (yi ⊗ ji)))) ⊖ (qi ⊗ (((xr ⊗ ui) ⊕ (xi ⊗ ur)) ⊕ ((yr ⊗ ji) ⊕ (yi ⊗ jr))))) ⊜ (((xr ⊗ ((qr ⊗ ur) ⊖ (qi ⊗ ui))) ⊖ (xi ⊗ ((qr ⊗ ui) ⊕ (qi ⊗ ur)))) ⊕ ((yr ⊗ ((qr ⊗ jr) ⊖ (qi ⊗ ji))) ⊖ (yi ⊗ ((qr ⊗ ji) ⊕ (qi ⊗ jr)))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re y) (C.im y) (C.re u) (C.im u) (C.re j) (C.im j)) ,
  (let open P.ℝ-Solver in solve 10 (λ qr qi xr xi yr yi ur ui jr ji →
    ((qr ⊗ (((xr ⊗ ui) ⊕ (xi ⊗ ur)) ⊕ ((yr ⊗ ji) ⊕ (yi ⊗ jr)))) ⊕ (qi ⊗ (((xr ⊗ ur) ⊖ (xi ⊗ ui)) ⊕ ((yr ⊗ jr) ⊖ (yi ⊗ ji))))) ⊜ (((xr ⊗ ((qr ⊗ ui) ⊕ (qi ⊗ ur))) ⊕ (xi ⊗ ((qr ⊗ ur) ⊖ (qi ⊗ ui)))) ⊕ ((yr ⊗ ((qr ⊗ ji) ⊕ (qi ⊗ jr))) ⊕ (yi ⊗ ((qr ⊗ jr) ⊖ (qi ⊗ ji)))))) P.≃-refl (C.re q) (C.im q) (C.re x) (C.im x) (C.re y) (C.im y) (C.re u) (C.im u) (C.re j) (C.im j))

secondGather : ∀ q x y d u v j →
  (q *C (((x *C v) +C (y *C u)) +C (d *C j))) ≈C
  (((x *C (q *C v)) +C (y *C (q *C u))) +C (d *C (q *C j)))
secondGather q x y d u v j = complexTrans
  (L.complexMultiplyDistributesLeft q ((x *C v) +C (y *C u)) (d *C j))
  (A.addCCongruent (firstGather q x y v u) (Transport.swapMiddle q d j))

-- Additive cancellation through the existing setoid difference.
cancelAdd : ∀ a b c → (a +C c) ≈C (b +C c) → a ≈C b
cancelAdd a b c e = Cross.zeroDifference a b
  (complexTrans (complexSym (J.subZero (a -C b)))
    (complexTrans (A.addCCongruent (C.≈C-refl _) (complexSym (J.sameSub c)))
      (complexTrans (complexSym (J.addStep a c b c))
        (complexTrans (A.subCCongruent e (C.≈C-refl _)) (J.sameSub _)))))


addRead : ∀ {q f g} → Read.Readout q f → Read.Readout q g → Read.Readout q (f ⊕s g)
addRead {q} {f} {g} a b =
  let eq : ∀ n → (Read.weight q f n +C Read.weight q g n) ≈C Read.weight q (f ⊕s g) n
      eq n = P.≃-symm (P.*-distribʳ-+ _ _ _) , P.≃-symm (P.*-distribʳ-+ _ _ _)
  in record
    { Read.value = Read.value a +C Read.value b
    ; Read.absolute = CP.complexAbsTransport eq
        (C.componentwise-absolute-series-convergent
          (CP.plusAbs _ _ (C.realAbsolute (Read.absolute a)) (C.realAbsolute (Read.absolute b)))
          (CP.plusAbs _ _ (C.imagAbsolute (Read.absolute a)) (C.imagAbsolute (Read.absolute b))))
    ; Read.converges = CP.complexLimitTransport eq
        (C.complex-series-converges-to
          (CP.plusConv (C.realConverges (Read.converges a)) (C.realConverges (Read.converges b)))
          (CP.plusConv (C.imagConverges (Read.converges a)) (C.imagConverges (Read.converges b)))) }

module At (inputs : Round11.BishopCutset) where
  module Lg = Log.At inputs
  module B = Lg.Around Fixed.p
  module S = B.D.S
  module O = Lg.F.O
  module FixedSource = Fixed.At inputs
  module Selected = Root.At inputs
  q = O.q Fixed.p
  j = Lg.G.j Fixed.p
  jv = O.Jvalue Fixed.p
  qnz = Lg.G.qNonzero Fixed.p

  -- Real slice readout is transported termwise using the original
  -- selected q equality; the imaginary stream is identically zero.
  literalRead : (f : Br.Readout) → Read.Readout q (Br.series f)
  literalRead f =
    let series = Br.series f
        terms = λ n → realC (Weight.weighted V.q series n)
        eq : ∀ n → terms n ≈C Read.weight q series n
        eq n = complexTrans
          ((P.*-comm (R.pow V.q n) (series n)) , (P.≃-symm (P.*-zeroʳ (series n))))
          (A.scaleCCongruent (complexSym (complexTrans
            (A.powCCongruent FixedSource.qRead n) (Root.realPow V.q n))) (series n))
    in record
      { Read.value = realC (Br.value f)
      ; Read.absolute = CP.complexAbsTransport eq
          (C.componentwise-absolute-series-convergent (Br.absolute f) Read.zeroAbs)
      ; Read.converges = CP.complexLimitTransport eq
          (C.complex-series-converges-to (Br.evaluation f) Read.zeroConv) }

  xR = literalRead Br.x
  yR = literalRead Br.y
  dxR = literalRead Br.x1
  dyR = literalRead Br.y1

  zR : Read.Readout q H.zeroSeries
  zR = Read.transport (λ _ → P.≃-refl) (Read.constantRead q R.0ℝ)

  original = O.junit Fixed.p
  inner = B.D.Ref.inner
  inz = B.D.Ref.inz
  inv = S.inv
  u = S.S.normal q
  hu = S.S.normalUpper q B.D.Ref.centerInside
  f = E.lift Unit.Junit
  g = S.g
  module Moments = M.At q inner inz f

  d1 : M.Stream (D.terms g u u)
  d1 = record
    { M.value = S.firstCoefficient q B.D.Ref.centerInside
    ; M.absolute = S.Jet.First.D.absolute u u hu hu
    ; M.converges = S.Jet.First.D.converges u u hu hu }

  d2 : M.Stream (T.terms g u u u)
  d2 = record
    { M.value = S.secondCoefficient q B.D.Ref.centerInside
    ; M.absolute = S.Jet.Second.absolute u u u hu hu hu
    ; M.converges = S.Jet.Second.converges u u u hu hu hu }

  firstE : Read.Readout q Flow.J1
  firstE = Eval.toReal (Eval.transport (E.liftD Unit.Junit) (Moments.first d1))

  secondE : Read.Readout q Flow.J2
  secondE = Eval.toReal (Eval.transport
    (λ n → complexTrans (E.dCong (E.liftD Unit.Junit) n) (E.liftD Flow.J1 n))
    (Moments.second d1 d2))

  firstERead : Read.value firstE ≈C (q *C B.D.J1)
  firstERead = L.complexMultiplyAssociative q inv (M.value d1)

  twiceJ2 : BishopComplex
  twiceJ2 = (q *C (q *C B.D.J2c)) +C (q *C (q *C B.D.J2c))

  secondERead : Read.value secondE ≈C ((q *C B.D.J1) +C twiceJ2)
  secondERead = A.addCCongruent firstERead
    (A.addCCongruent (unscale2 q inv (M.value d2)) (unscale2 q inv (M.value d2)))

  l1 = Read.subtract firstE original
  l2 = addRead (Read.subtract secondE (addRead firstE firstE)) original

  firstClear : (q *C B.euler1) ≈C Read.value l1
  firstClear = complexTrans
    (A.mulCCongruent (C.≈C-refl _) (Divide.read q qnz (B.D.J1 -C j)))
    (complexTrans (Alg.mulSub q B.D.J1 j)
      (A.subCCongruent (complexSym firstERead) (O.qj Fixed.p)))

  secondClearRead : (q *C (B.eulerTaylor2 +C B.eulerTaylor2)) ≈C Read.value l2
  secondClearRead =
    complexTrans (A.mulCCongruent (C.≈C-refl _) (doubleTaylor q B.D.j1 B.D.j2))
      (complexTrans (A.mulCCongruent (C.≈C-refl _)
        (A.addCCongruent (C.≈C-refl _)
          (A.addCCongruent
            (A.mulCCongruent (C.≈C-refl _) (Divide.read q qnz (B.D.J2c -C B.D.j1)))
            (A.mulCCongruent (C.≈C-refl _) (Divide.read q qnz (B.D.J2c -C B.D.j1))))))
        (complexTrans (secondClear q B.D.j1 B.D.J2c)
          (complexTrans (A.subCCongruent (C.≈C-refl _)
            (complexTrans firstClear (A.subCCongruent firstERead (C.≈C-refl _))))
            (complexTrans (secondCombine (q *C B.D.J1) twiceJ2 jv)
              (A.addCCongruent (A.subCCongruent (complexSym secondERead)
                (A.addCCongruent (complexSym firstERead) (complexSym firstERead))) (C.≈C-refl _))))))

  firstEval = addRead (Read.product xR l1) (Read.product yR original)
  secondEval = addRead (addRead (Read.product xR l2)
    (Read.product (addRead dxR yR) l1)) (Read.product dyR original)

  firstZero : Read.value firstEval ≈C A.zeroC
  firstZero = Read.same (Read.transport Flow.first firstEval) zR
  secondZero : Read.value secondEval ≈C A.zeroC
  secondZero = Read.same (Read.transport Flow.second secondEval) zR

  X = realC QJ.X
  Y = realC QJ.Y
  DX = realC QJ.x1
  DY = realC QJ.y1
  J0 = realC QJ.j
  a = realC QJ.a
  b = realC QJ.b
  jRead : j ≈C J0
  jRead = Selected.selectedSame

  firstLaw : ((X *C B.euler1) +C (Y *C j)) ≈C A.zeroC
  firstLaw = Cancel.cancelLeft q _ _ qnz
    (complexTrans (firstGather q X Y B.euler1 j)
      (complexTrans (A.addCCongruent (A.mulCCongruent (C.≈C-refl _) firstClear)
        (A.mulCCongruent (C.≈C-refl _) (O.qj Fixed.p)))
        (complexTrans firstZero (complexSym (L.complexMultiplyRightZero q)))))

  secondLaw : (((X *C (B.eulerTaylor2 +C B.eulerTaylor2)) +C
    ((DX +C Y) *C B.euler1)) +C (DY *C j)) ≈C A.zeroC
  secondLaw = Cancel.cancelLeft q _ _ qnz
    (complexTrans (secondGather q X (DX +C Y) DY B.euler1 (B.eulerTaylor2 +C B.eulerTaylor2) j)
      (complexTrans (A.addCCongruent
        (A.addCCongruent (A.mulCCongruent (C.≈C-refl _) secondClearRead)
          (A.mulCCongruent (C.≈C-refl _) firstClear))
        (A.mulCCongruent (C.≈C-refl _) (O.qj Fixed.p)))
        (complexTrans secondZero (complexSym (L.complexMultiplyRightZero q)))))

  candidateFirst : ((X *C a) +C (Y *C J0)) ≈C A.zeroC
  candidateFirst = complexTrans
    (A.addCCongruent (Root.realMul QJ.X QJ.a)
      (complexTrans (L.complexMultiplyCommutative Y J0) (Root.realMul QJ.j QJ.Y)))
    (complexTrans (Root.realAdd (QJ.X * QJ.a) (QJ.j * QJ.Y)) (QJ.firstZ , P.≃-refl))

  candidateSecond : (((X *C b) +C ((DX +C Y) *C a)) +C (DY *C J0)) ≈C A.zeroC
  candidateSecond = complexTrans
    (A.addCCongruent
      (A.addCCongruent (Root.realMul QJ.X QJ.b)
        (complexTrans (A.mulCCongruent (Root.realAdd QJ.x1 QJ.Y) (C.≈C-refl _))
          (Root.realMul (QJ.x1 + QJ.Y) QJ.a)))
      (complexTrans (L.complexMultiplyCommutative DY J0) (Root.realMul QJ.j QJ.y1)))
    (complexTrans (A.addCCongruent (Root.realAdd (QJ.X * QJ.b) ((QJ.x1 + QJ.Y) * QJ.a)) (C.≈C-refl _))
      (complexTrans (Root.realAdd _ _) (QJ.secondZ , P.≃-refl)))

  eulerRead : B.euler1 ≈C a
  eulerRead = Cancel.cancelLeft X _ _ (NZ.complexNonzeroFromRealApart Literal.xNZ)
    (cancelAdd (X *C B.euler1) (X *C a) (Y *C J0)
      (complexTrans (A.addCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (complexSym jRead)))
        (complexTrans firstLaw (complexSym candidateFirst))))

  doubleEulerRead : (B.eulerTaylor2 +C B.eulerTaylor2) ≈C b
  doubleEulerRead = Cancel.cancelLeft X _ _ (NZ.complexNonzeroFromRealApart Literal.xNZ)
    (cancelAdd (X *C (B.eulerTaylor2 +C B.eulerTaylor2)) (X *C b) ((DX +C Y) *C a)
      (cancelAdd _ _ (DY *C J0)
        (complexTrans (A.addCCongruent
          (A.addCCongruent (C.≈C-refl _) (A.mulCCongruent (C.≈C-refl _) (complexSym eulerRead)))
          (A.mulCCongruent (C.≈C-refl _) (complexSym jRead)))
          (complexTrans secondLaw (complexSym candidateSecond)))))

  halfDouble : ∀ z → (realC ((+ 1 / 2) ⋆) *C (z +C z)) ≈C z
  halfDouble z =
    (let open P.ℝ-Solver in solve 2 (λ x y → Κ (+ 1 / 2) ⊗ (x ⊕ x) ⊖ Κ 0ℚᵘ ⊗ (y ⊕ y) ⊜ x)
      P.≃-refl (C.re z) (C.im z)) ,
    (let open P.ℝ-Solver in solve 2 (λ x y → Κ (+ 1 / 2) ⊗ (y ⊕ y) ⊕ Κ 0ℚᵘ ⊗ (x ⊕ x) ⊜ y)
      P.≃-refl (C.re z) (C.im z))

  secondEulerRead : B.eulerTaylor2 ≈C realC (((+ 1 / 2) ⋆) * QJ.b)
  secondEulerRead = complexTrans (complexSym (halfDouble B.eulerTaylor2))
    (complexTrans (A.mulCCongruent (C.≈C-refl _) doubleEulerRead) (Root.realMul ((+ 1 / 2) ⋆) QJ.b))
