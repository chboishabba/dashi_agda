module DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact where

-- SOURCE-WRITTEN, kernel pending. The original descending integer
-- packet is evaluated on the same J=q*j, not on a fitted root.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41ActualSeriesEvaluationExact as Actual
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Coeff
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC)
open G using (Series; _⊕s_; scale)
open Comp using (complexTrans; complexSym)

realC : R.ℝ → BishopComplex
realC a = C.complex a R.0ℝ

addWeight : ∀ q f g n → (Read.weight q f n +C Read.weight q g n) ≈C Read.weight q (f ⊕s g) n
addWeight q f g n =
  (let open P.ℝ-Solver in solve 3 (λ a b x → a ⊗ x ⊕ b ⊗ x ⊜ (a ⊕ b) ⊗ x)
    P.≃-refl (f n) (g n) (C.re (powC q n))) ,
  (let open P.ℝ-Solver in solve 3 (λ a b x → a ⊗ x ⊕ b ⊗ x ⊜ (a ⊕ b) ⊗ x)
    P.≃-refl (f n) (g n) (C.im (powC q n)))

addRead : ∀ {q f g} → Read.Readout q f → Read.Readout q g → Read.Readout q (f ⊕s g)
addRead {q} {f} {g} a b =
  let x = Read.weight q f; y = Read.weight q g
      ab = C.componentwise-absolute-series-convergent
        (CP.plusAbs (C.realTerms x) (C.realTerms y) (C.realAbsolute (Read.absolute a)) (C.realAbsolute (Read.absolute b)))
        (CP.plusAbs (C.imagTerms x) (C.imagTerms y) (C.imagAbsolute (Read.absolute a)) (C.imagAbsolute (Read.absolute b)))
      cv = C.complex-series-converges-to
        (CP.plusConv (C.realConverges (Read.converges a)) (C.realConverges (Read.converges b)))
        (CP.plusConv (C.imagConverges (Read.converges a)) (C.imagConverges (Read.converges b)))
  in record { value = Read.value a +C Read.value b
    ; absolute = CP.complexAbsTransport (addWeight q f g) ab
    ; converges = CP.complexLimitTransport (addWeight q f g) cv }

scaleRead : ∀ {q f} a → Read.Readout q f → Read.Readout q (scale a f)
scaleRead {q} {f} a ev = Read.transport (G.constantScale a f)
  (Read.product (Read.constantRead q a) ev)

powerRead : ∀ {q f} → Read.Readout q f → ∀ n → Read.Readout q (H.power f n)
powerRead {q} ev zero = Read.constantRead q R.1ℝ
powerRead ev (suc n) = Read.product ev (powerRead ev n)

powerValue : ∀ {q f} (ev : Read.Readout q f) n →
  Read.value (powerRead ev n) ≈C powC (Read.value ev) n
powerValue ev zero = C.≈C-refl _
powerValue ev (suc n) = A.mulCCongruent (C.≈C-refl _) (powerValue ev n)

degree : List ℚᵘ → Nat
degree [] = zero
degree (c ∷ cs) = length cs

poly : BishopComplex → List ℚᵘ → BishopComplex
poly j [] = A.zeroC
poly j (c ∷ cs) = (realC (c ⋆) *C powC j (length cs)) +C poly j cs

hom : BishopComplex → BishopComplex → List ℚᵘ → BishopComplex
hom q v [] = A.zeroC
hom q v (c ∷ cs) = (realC (c ⋆) *C powC v (length cs)) +C (q *C hom q v cs)

polyCong : ∀ {a b} → a ≈C b → ∀ cs → poly a cs ≈C poly b cs
polyCong h [] = C.≈C-refl _
polyCong h (c ∷ cs) = A.addCCongruent
  (A.mulCCongruent (C.≈C-refl _) (A.powCCongruent h (length cs))) (polyCong h cs)

headClear : ∀ q j v c n → (q *C j) ≈C v →
  (powC q n *C (c *C powC j n)) ≈C (c *C powC v n)
headClear q j v c n h = complexTrans (complexSym (L.complexMultiplyAssociative (powC q n) c (powC j n)))
  (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative (powC q n) c) (C.≈C-refl _))
    (complexTrans (L.complexMultiplyAssociative c (powC q n) (powC j n))
      (A.mulCCongruent (C.≈C-refl _) (complexTrans (complexSym (Gen.powProduct q j n)) (A.powCCongruent h n)))))

clear : ∀ q j v cs → (q *C j) ≈C v →
  (powC q (degree cs) *C poly j cs) ≈C hom q v cs
clear q j v [] h = L.complexMultiplyRightZero A.oneC
clear q j v (c ∷ []) h =
  complexTrans (L.complexMultiplyDistributesLeft A.oneC (realC (c ⋆) *C A.oneC) A.zeroC)
    (A.addCCongruent (headClear q j v (realC (c ⋆)) zero h)
      (complexTrans (L.complexMultiplyRightZero A.oneC) (complexSym (L.complexMultiplyRightZero q))))
clear q j v (c ∷ d ∷ cs) h =
  complexTrans (L.complexMultiplyDistributesLeft (powC q (suc (length cs))) _ _)
    (A.addCCongruent (headClear q j v (realC (c ⋆)) (suc (length cs)) h)
      (complexTrans (L.complexMultiplyAssociative q (powC q (length cs)) (poly j (d ∷ cs)))
        (A.mulCCongruent (C.≈C-refl _) (clear q j v (d ∷ cs) h))))

module At (inputs : Round11.BishopCutset) where
  module V = Actual.At inputs
  open V using (t; q; qtRead; Jvalue)

  columnRead : ∀ p cs → Read.Readout (t p) (Coeff.column cs)
  columnRead p [] = Read.constantRead (t p) R.0ℝ
  columnRead p (c ∷ cs) = addRead
    (scaleRead (c ⋆) (powerRead (qtRead p) (length cs)))
    (Read.product (Eval.monoRead (t p) 41) (columnRead p cs))

  columnValue : ∀ p cs → Read.value (columnRead p cs) ≈C hom (q p) (Jvalue p) cs
  columnValue p [] = C.≈C-refl _
  columnValue p (c ∷ cs) = A.addCCongruent
    (A.mulCCongruent (C.≈C-refl _) (powerValue (qtRead p) (length cs)))
    (A.mulCCongruent (complexTrans (Eval.monoValue (t p) 41) (V.Rm.tPower p)) (columnValue p cs))

  columnQ : ∀ p cs → (powC (q p) (degree cs) *C poly (V.A0.G.j p) cs) ≈C Read.value (columnRead p cs)
  columnQ p cs = complexTrans (clear (q p) (V.A0.G.j p) (Jvalue p) cs (V.A0.qj p))
    (complexSym (columnValue p cs))

  diagonalColumn : ∀ p → Eval.Eval (t p) (E.lift Coeff.diagColumn)
  diagonalColumn p = Eval.fromReal (columnRead p Packet.diagonal)

  sliceColumn : ∀ p → Eval.Eval (t p) (E.lift Coeff.sliceColumn)
  sliceColumn p = Eval.fromReal (columnRead p Packet.slice)

  diagonalT : ∀ p → (powC (t p) 3362 *C poly (V.A0.G.j p) Packet.diagonal) ≈C Eval.value (diagonalColumn p)
  diagonalT p = complexTrans (A.mulCCongruent
    (complexTrans (complexSym (Ram.powPow (t p) 41 82)) (A.powCCongruent (V.Rm.tPower p) 82))
    (C.≈C-refl _)) (columnQ p Packet.diagonal)

  sliceT : ∀ p → (powC (t p) 1722 *C poly (V.A0.G.j p) Packet.slice) ≈C Eval.value (sliceColumn p)
  sliceT p = complexTrans (A.mulCCongruent
    (complexTrans (complexSym (Ram.powPow (t p) 41 42)) (A.powCCongruent (V.Rm.tPower p) 42))
    (C.≈C-refl _)) (columnQ p Packet.slice)
