module DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact where

-- SOURCE-WRITTEN, kernel pending. Exact symmetric finite matrix
-- evaluation and reverse original fixed slice. The only analytic
-- premise is the full original product identity; no separate
-- symmetry or generic-distinctness assumption is used.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_∸_)
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (_,_)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.Rational.Unnormalised as Q using (_/_; ℚᵘ; 0ℚᵘ; 1ℚᵘ)
open import Agda.Builtin.Equality using (_≡_)
import Real as R
open R using (_⋆; _≃_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact as M
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as Root
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Literal
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as CM
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open N using (sumC; sumCong; sumMul)
open Poly using (realC)

sumAdd : ∀ {n} (f g : Fin n → BishopComplex) →
  sumC (λ i → f i +C g i) ≈C (sumC f +C sumC g)
sumAdd {zero} f g = complexSym (L.complexAddRightIdentity A.zeroC)
sumAdd {suc n} f g =
  complexTrans (A.addCCongruent (C.≈C-refl _)
    (sumAdd (λ i → f (Fin.suc i)) (λ i → g (Fin.suc i))))
    (Shift.addShuffle (f Fin.zero) (g Fin.zero)
      (sumC (λ i → f (Fin.suc i))) (sumC (λ i → g (Fin.suc i))))

sumZero : ∀ n → sumC {n} (λ _ → A.zeroC) ≈C A.zeroC
sumZero zero = C.≈C-refl _
sumZero (suc n) = complexTrans (A.addCCongruent (C.≈C-refl _) (sumZero n)) (L.complexAddRightIdentity _)

fubini : ∀ {n m} (f : Fin n → Fin m → BishopComplex) →
  sumC (λ i → sumC (f i)) ≈C sumC (λ j → sumC (λ i → f i j))
fubini {zero} {m} f = complexSym (sumZero m)
fubini {suc n} {m} f =
  complexTrans (A.addCCongruent (C.≈C-refl _) (fubini (λ i j → f (Fin.suc i) j)))
    (complexSym (sumAdd (f Fin.zero) (λ j → sumC (λ i → f (Fin.suc i) j))))

expo : Fin 43 → Nat
expo i = 42 ∸ toℕ i

Coefficient : Set
Coefficient = Nat → Nat → ℤ

term : Coefficient → BishopComplex → BishopComplex → Fin 43 → Fin 43 → BishopComplex
term c x y i j = (realC (I.embed (c (expo i) (expo j))) *C powC y (expo j)) *C powC x (expo i)

matrix : Coefficient → BishopComplex → BishopComplex → BishopComplex
matrix c x y = sumC (λ i → sumC (term c x y i))

Symmetric : Coefficient → Set
Symmetric c = ∀ i j → c (expo i) (expo j) ≡ c (expo j) (expo i)

swapTerm : ∀ c x y → Symmetric c → ∀ i j → term c x y i j ≈C term c y x j i
swapTerm c x y eq i j =
  complexTrans (A.mulCCongruent (A.mulCCongruent (I.embedCong (eq i j) , P.≃-refl) (C.≈C-refl _)) (C.≈C-refl _))
    (complexTrans (L.complexMultiplyAssociative _ _ _)
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (L.complexMultiplyCommutative _ _))
        (complexSym (L.complexMultiplyAssociative _ _ _))))

symmetric : ∀ c → Symmetric c → ∀ x y → matrix c x y ≈C matrix c y x
symmetric c eq x y =
  complexTrans (fubini (term c x y))
    (sumCong _ _ (λ j → sumCong _ _ (λ i → swapTerm c x y eq i j)))

matrixCong : ∀ c {x x' y y'} → x ≈C x' → y ≈C y' → matrix c x y ≈C matrix c x' y'
matrixCong c hx hy = sumCong _ _ (λ i → sumCong _ _ (λ j →
  A.mulCCongruent (A.mulCCongruent (C.≈C-refl _) (A.powCCongruent hy (expo j)))
    (A.powCCongruent hx (expo i))))

zsum : ∀ {n} → (Fin n → ℤ) → ℤ
zsum {zero} f = + 0
zsum {suc n} f = Z._+_ (f Fin.zero) (zsum (λ i → f (Fin.suc i)))

zsumRead : ∀ {n} (f : Fin n → ℤ) →
  sumC (λ i → realC (I.embed (f i))) ≈C realC (I.embed (zsum f))
zsumRead {zero} f = C.≈C-refl _
zsumRead {suc n} f =
  complexTrans (A.addCCongruent (C.≈C-refl _) (zsumRead (λ i → f (Fin.suc i))))
    (complexTrans (Root.realAdd _ _) (P.≃-symm (I.embedAdd _ _) , P.≃-refl))

zpowRead : ∀ a n → powC (realC (I.embed a)) n ≈C realC (I.embed (M.zpow a n))
zpowRead a zero = C.≈C-refl _
zpowRead a (suc n) =
  complexTrans (A.mulCCongruent (C.≈C-refl _) (zpowRead a n))
    (complexTrans (Root.realMul _ _) (P.≃-symm (I.embedMul _ _) , P.≃-refl))

sliceCoefficient : Coefficient → Fin 43 → ℤ
sliceCoefficient c i = zsum (λ j → Z._*_ (c (expo i) (expo j)) (M.zpow Cert.K (expo j)))

SliceGate : Coefficient → Set
SliceGate c = ∀ i → (sliceCoefficient c i / 1) Q.≃ Literal.coeff (toℕ i) Packet.slice

KRead : Shift.K ≈C realC (I.embed Cert.K)
KRead = C.≈C-refl _

innerRead : ∀ c x i →
  sumC (term c x Shift.K i) ≈C (realC (I.embed (sliceCoefficient c i)) *C powC x (expo i))
innerRead c x i =
  complexTrans (sumMul (λ j → realC (I.embed (c (expo i) (expo j))) *C powC Shift.K (expo j)) (powC x (expo i)))
    (A.mulCCongruent
      (complexTrans (sumCong _ _ (λ j →
        complexTrans (A.mulCCongruent (C.≈C-refl _)
          (complexTrans (A.powCCongruent KRead (expo j)) (zpowRead Cert.K (expo j))))
          (complexTrans (Root.realMul _ _) (P.≃-symm (I.embedMul _ _) , P.≃-refl))))
        (zsumRead _)) (C.≈C-refl _))

-- Descending packet enumeration is exactly the existing polynomial
-- evaluator. No reindexing through an assumed inverse j is needed.
polySum : ∀ z cs → Poly.poly z cs ≈C
  sumC (λ (i : Fin (length cs)) →
    realC (Literal.coeff (toℕ i) cs ⋆) *C powC z (length cs ∸ suc (toℕ i)))
polySum z [] = C.≈C-refl _
polySum z (c ∷ cs) = A.addCCongruent (C.≈C-refl _) (polySum z cs)

fixedSlice : ∀ c → SliceGate c → ∀ y → matrix c y Shift.K ≈C Poly.poly y Packet.slice
fixedSlice c gate y =
  complexTrans (sumCong _ _ (λ i → complexTrans (innerRead c y i)
    (A.mulCCongruent (P.⋆-cong (gate i) , P.≃-refl) (C.≈C-refl _))))
    (complexSym (polySum y Packet.slice))

module At (inputs : Round11.BishopCutset) where
  module H = Cross.At inputs
  module SR = Root.At inputs

  -- Same global producer used for all real target parameters, rather
  -- than an independent reverse-slice analytic postulate.
  FullIdentity : Coefficient → Set
  FullIdentity c = ∀ p (y : R.ℝ) → H.G.product p (realC y) ≈C matrix c (H.G.j p) (realC y)

  reverseSlice : ∀ c → Symmetric c → SliceGate c → FullIdentity c →
    CM.CMRoot → ∀ y → H.G.product Fixed.p (realC y) ≈C Poly.poly (realC y) Packet.slice
  reverseSlice c sym gate full hj y =
    complexTrans (full Fixed.p y)
      (complexTrans (matrixCong c (complexTrans SR.selectedSame (hj , P.≃-refl)) (C.≈C-refl _))
        (complexTrans (symmetric c sym Shift.K (realC y)) (fixedSlice c gate (realC y))))
