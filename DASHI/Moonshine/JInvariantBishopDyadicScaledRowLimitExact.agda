module DASHI.Moonshine.JInvariantBishopDyadicScaledRowLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. Pointwise dyadic lattice summand limits
-- on the original exp and the original rational Fourier row functions.
-- The lower-degree terms are retained until h tends to zero.
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _*_; _⋆; _≤_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)
open Rat using (square; cube)

squareR fourthR sixthR : ℝ → ℝ
squareR h = h * h
fourthR h = squareR h * squareR h
sixthR h = fourthR h * squareR h

scaledX : ∀ h q i → (q *C square (scaleC (R.- h) i)) ≈C
  scaleC (squareR h) (q *C square i)
scaledX h (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → (a ⊗ (((⊝ h) ⊗ c) ⊗ ((⊝ h) ⊗ c) ⊖ ((⊝ h) ⊗ d) ⊗ ((⊝ h) ⊗ d)) ⊖ b ⊗ (((⊝ h) ⊗ c) ⊗ ((⊝ h) ⊗ d) ⊕ ((⊝ h) ⊗ d) ⊗ ((⊝ h) ⊗ c))) ⊜ ((h ⊗ h) ⊗ (a ⊗ (c ⊗ c ⊖ d ⊗ d) ⊖ b ⊗ (c ⊗ d ⊕ d ⊗ c)))) P.≃-refl h a b c d)
  ,
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → (a ⊗ (((⊝ h) ⊗ c) ⊗ ((⊝ h) ⊗ d) ⊕ ((⊝ h) ⊗ d) ⊗ ((⊝ h) ⊗ c)) ⊕ b ⊗ (((⊝ h) ⊗ c) ⊗ ((⊝ h) ⊗ c) ⊖ ((⊝ h) ⊗ d) ⊗ ((⊝ h) ⊗ d))) ⊜ ((h ⊗ h) ⊗ (a ⊗ (c ⊗ d ⊕ d ⊗ c) ⊕ b ⊗ (c ⊗ c ⊖ d ⊗ d)))) P.≃-refl h a b c d)

scaled4Read : ∀ h x → scaleC (fourthR h) (Row.P4 x) ≈C
  (scaleC (squareR h) (scaleC (squareR h) x) +C Row.scale 6 (square (scaleC (squareR h) x)))
scaled4Read h (C.complex x y) =
  (let open P.ℝ-Solver in solve 3
    (λ h x y → (((h ⊗ h) ⊗ (h ⊗ h)) ⊗ (x ⊕ (Κ (+ 6 / 1) ⊗ (x ⊗ x ⊖ y ⊗ y)))) ⊜ (((h ⊗ h) ⊗ ((h ⊗ h) ⊗ x)) ⊕ (Κ (+ 6 / 1) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ x) ⊖ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ y))))) P.≃-refl h x y)
  ,
  (let open P.ℝ-Solver in solve 3
    (λ h x y → (((h ⊗ h) ⊗ (h ⊗ h)) ⊗ (y ⊕ (Κ (+ 6 / 1) ⊗ (x ⊗ y ⊕ y ⊗ x)))) ⊜ (((h ⊗ h) ⊗ ((h ⊗ h) ⊗ y)) ⊕ (Κ (+ 6 / 1) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ y) ⊕ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ x))))) P.≃-refl h x y)

scaled6Read : ∀ h x → scaleC (sixthR h) (Row.P6 x) ≈C
  ((scaleC (fourthR h) (scaleC (squareR h) x) +C Row.scale 30 (scaleC (squareR h) (square (scaleC (squareR h) x)))) +C Row.scale 120 (cube (scaleC (squareR h) x)))
scaled6Read h (C.complex x y) =
  (let open P.ℝ-Solver in solve 3
    (λ h x y → ((((h ⊗ h) ⊗ (h ⊗ h)) ⊗ (h ⊗ h)) ⊗ ((x ⊕ (Κ (+ 30 / 1) ⊗ (x ⊗ x ⊖ y ⊗ y))) ⊕ (Κ (+ 120 / 1) ⊗ (x ⊗ (x ⊗ x ⊖ y ⊗ y) ⊖ y ⊗ (x ⊗ y ⊕ y ⊗ x))))) ⊜ (((((h ⊗ h) ⊗ (h ⊗ h)) ⊗ ((h ⊗ h) ⊗ x)) ⊕ (Κ (+ 30 / 1) ⊗ ((h ⊗ h) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ x) ⊖ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ y))))) ⊕ (Κ (+ 120 / 1) ⊗ (((h ⊗ h) ⊗ x) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ x) ⊖ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ y)) ⊖ ((h ⊗ h) ⊗ y) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ y) ⊕ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ x)))))) P.≃-refl h x y)
  ,
  (let open P.ℝ-Solver in solve 3
    (λ h x y → ((((h ⊗ h) ⊗ (h ⊗ h)) ⊗ (h ⊗ h)) ⊗ ((y ⊕ (Κ (+ 30 / 1) ⊗ (x ⊗ y ⊕ y ⊗ x))) ⊕ (Κ (+ 120 / 1) ⊗ (x ⊗ (x ⊗ y ⊕ y ⊗ x) ⊕ y ⊗ (x ⊗ x ⊖ y ⊗ y))))) ⊜ (((((h ⊗ h) ⊗ (h ⊗ h)) ⊗ ((h ⊗ h) ⊗ y)) ⊕ (Κ (+ 30 / 1) ⊗ ((h ⊗ h) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ y) ⊕ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ x))))) ⊕ (Κ (+ 120 / 1) ⊗ (((h ⊗ h) ⊗ x) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ y) ⊕ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ x)) ⊕ ((h ⊗ h) ⊗ y) ⊗ (((h ⊗ h) ⊗ x) ⊗ ((h ⊗ h) ⊗ x) ⊖ ((h ⊗ h) ⊗ y) ⊗ ((h ⊗ h) ⊗ y)))))) P.≃-refl h x y)

scaleZeroLeft : ∀ z → scaleC R.0ℝ z ≈C A.zeroC
scaleZeroLeft (C.complex a b) =
  (let open P.ℝ-Solver in solve 1 (λ a → Κ 0ℚᵘ ⊗ a ⊜ Κ 0ℚᵘ) P.≃-refl a) ,
  (let open P.ℝ-Solver in solve 1 (λ b → Κ 0ℚᵘ ⊗ b ⊜ Κ 0ℚᵘ) P.≃-refl b)

scaleConst : ∀ n {f : Nat → BishopComplex} {z} → Lim.Conv f z →
  Lim.Conv (λ k → Row.scale n (f k)) (Row.scale n z)
scaleConst n cv = Inv.scaleConv (Power.constantConverges ((+ n / 1) ⋆)) cv

module AtDirection (T : Cartesian.BishopSetoidComplexTranscendentals)
  (z : BishopComplex) (nz : Rec.BishopComplexNonzero z)
  (M : ℝ) (upper : Upper.BishopComplexNormSquareUpperRadius z M)
  (h : Nat → ℝ) (small : ∀ n → ∣ h n ∣ ≤ R.1ℝ)
  (null : Seq._ConvergesTo_ h R.0ℝ)
  (guard : ∀ n → Rec.BishopComplexNonzero
    (Row.gapMinus (Weld.originalBishopExpOnSeries T (scaleC (h n) z)))) where

  module I = Inv.AtDirection T z nz M upper h small null guard
  q = I.q
  v = I.v
  V = Rec.reciprocalC z nz
  X : Nat → BishopComplex
  X n = Row.X (q n) (guard n)

  Y : Nat → BishopComplex
  Y n = q n *C square (v n)
  yRead : ∀ n → Y n ≈C scaleC (squareR (h n)) (X n)
  yRead n = scaledX (h n) (q n) (Rec.reciprocalC (Row.gapMinus (q n)) (guard n))

  yConverges : Lim.Conv Y (square V)
  yConverges = Lim.limitTransport (L.complexMultiplyLeftIdentity (square V))
    (Inv.mulConv I.qConverges (Inv.mulConv I.reciprocalConverges I.reciprocalConverges))

  h2Null : Seq._ConvergesTo_ (λ n → squareR (h n)) R.0ℝ
  h2Null = Seq.xₙ→x∧x≃y⇒xₙ→y (Inv.mulR null null)
    (let open P.ℝ-Solver in solve 0 (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl)

  h4Null : Seq._ConvergesTo_ (λ n → fourthR (h n)) R.0ℝ
  h4Null = Seq.xₙ→x∧x≃y⇒xₙ→y (Inv.mulR h2Null h2Null)
    (let open P.ℝ-Solver in solve 0 (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl)

  scaled4 : Nat → BishopComplex
  scaled4 n = scaleC (fourthR (h n)) (Row.P4 (X n))
  scaled6 : Nat → BishopComplex
  scaled6 n = scaleC (sixthR (h n)) (Row.P6 (X n))

  reduced4 : Nat → BishopComplex
  reduced4 n = scaleC (squareR (h n)) (Y n) +C Row.scale 6 (square (Y n))
  reduced6 : Nat → BishopComplex
  reduced6 n = (scaleC (fourthR (h n)) (Y n) +C
    Row.scale 30 (scaleC (squareR (h n)) (square (Y n)))) +C Row.scale 120 (cube (Y n))

  row4Read : ∀ n → scaled4 n ≈C reduced4 n
  row4Read n = complexTrans (scaled4Read (h n) (X n))
    (A.addCCongruent (A.scaleCCongruent (complexSym (yRead n)) (squareR (h n)))
      (Row.scaleCong 6 (A.mulCCongruent (complexSym (yRead n)) (complexSym (yRead n)))))

  row6Read : ∀ n → scaled6 n ≈C reduced6 n
  row6Read n =
    let eq = complexSym (yRead n)
        sqEq = A.mulCCongruent eq eq
    in complexTrans (scaled6Read (h n) (X n))
      (A.addCCongruent
        (A.addCCongruent (A.scaleCCongruent eq (fourthR (h n)))
          (Row.scaleCong 30 (A.scaleCCongruent sqEq (squareR (h n)))))
        (Row.scaleCong 120 (A.mulCCongruent eq sqEq)))

  -- The desired constants are 3! and 5!, with the original sign of
  -- (2*pi*i)^k retained inside the complex reciprocal power.
  limit4 : Lim.Conv scaled4 (Row.scale 6 (square (square V)))
  limit4 = Lim.convTransport (λ n → complexSym (row4Read n))
    (Lim.limitTransport (L.complexAddLeftIdentity _)
      (Lim.addConv (Lim.limitTransport (scaleZeroLeft _) (Inv.scaleConv h2Null yConverges))
        (scaleConst 6 (Inv.mulConv yConverges yConverges))))

  limit6 : Lim.Conv scaled6 (Row.scale 120 (cube (square V)))
  limit6 =
    let ys = Inv.mulConv yConverges yConverges
        yc = Inv.mulConv yConverges ys
        first = Lim.limitTransport (scaleZeroLeft _) (Inv.scaleConv h4Null yConverges)
        second = Lim.limitTransport (Row.scaleCong 30 (C.≈C-refl _))
          (scaleConst 30 (Lim.limitTransport (scaleZeroLeft _) (Inv.scaleConv h2Null ys)))
        secondZero = Lim.limitTransport (let open P.ℝ-Solver in
          (solve 0 (Κ (+ 30 / 1) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl ,
           solve 0 (Κ (+ 30 / 1) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl)) second
    in Lim.convTransport (λ n → complexSym (row6Read n))
      (Lim.limitTransport (L.complexAddLeftIdentity _)
        (Lim.addConv (Lim.limitTransport (L.complexAddLeftIdentity _) (Lim.addConv first secondZero))
          (scaleConst 120 yc)))
