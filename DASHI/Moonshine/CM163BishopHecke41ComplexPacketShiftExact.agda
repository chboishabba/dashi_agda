module DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact where

-- SOURCE-WRITTEN, kernel pending. Extend the original real Horner
-- shift to the complex carrier of the actual Hecke product.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (_,_)
import Data.Rational.Unnormalised as Q
open Q using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as RealPoly
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; _-C_; powC)
open Comp using (complexTrans; complexSym)
open Poly using (realC)

K : BishopComplex
K = realC (Shift.Kq ⋆)

asc : BishopComplex → List ℚᵘ → BishopComplex
asc z [] = A.zeroC
asc z (c ∷ cs) = realC (c ⋆) +C (z *C asc z cs)

desc : BishopComplex → BishopComplex → List ℚᵘ → BishopComplex
desc z a [] = a
desc z a (c ∷ cs) = desc z (realC (c ⋆) +C z *C a) cs

descCong : ∀ {z w a b} → z ≈C w → a ≈C b → ∀ cs → desc z a cs ≈C desc w b cs
descCong h k [] = k
descCong h k (c ∷ cs) = descCong h
  (A.addCCongruent (C.≈C-refl _) (A.mulCCongruent h k)) cs

-- Ring identity used by both the Horner and coefficient shift routes.
addShuffle : ∀ a b c d → ((a +C b) +C (c +C d)) ≈C ((a +C c) +C (b +C d))
addShuffle a b c d =
  (let open P.ℝ-Solver in solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
    P.≃-refl (C.re a) (C.re b) (C.re c) (C.re d)) ,
  (let open P.ℝ-Solver in solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
    P.≃-refl (C.im a) (C.im b) (C.im c) (C.im d))

descRead : ∀ z a cs → desc z a cs ≈C ((a *C powC z (length cs)) +C Poly.poly z cs)
descRead z a [] = complexSym (complexTrans
  (A.addCCongruent (L.complexMultiplyRightIdentity a) (C.≈C-refl _))
  (L.complexAddRightIdentity a))
descRead z a (c ∷ cs) =
  let p = powC z (length cs); y = Poly.poly z cs; k = realC (c ⋆)
  in complexTrans (descRead z (k +C z *C a) cs)
    (complexTrans (A.addCCongruent (L.complexMultiplyDistributesRight k (z *C a) p) (C.≈C-refl _))
      (complexTrans (A.addCCongruent (L.complexAddCommutative (k *C p) ((z *C a) *C p)) (C.≈C-refl _))
        (complexTrans (L.complexAddAssociative ((z *C a) *C p) (k *C p) y)
          (A.addCCongruent
            (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative z a) (C.≈C-refl _))
              (L.complexMultiplyAssociative a z p)) (C.≈C-refl _)))))

descZero : ∀ z cs → desc z A.zeroC cs ≈C Poly.poly z cs
descZero z cs = complexTrans (descRead z A.zeroC cs)
  (complexTrans (A.addCCongruent (L.complexMultiplyLeftZero _) (C.≈C-refl _))
    (L.complexAddLeftIdentity _))

ratRead : ∀ a b → realC ((a Q.+ (Shift.Kq Q.* b)) ⋆) ≈C (realC (a ⋆) +C K *C realC (b ⋆))
ratRead a b = complexTrans
  (P.⋆-distrib-+ a (Shift.Kq Q.* b) , P.≃-refl)
  (complexTrans (P.+-cong P.≃-refl (P.⋆-distrib-* Shift.Kq b) , P.≃-refl)
    (complexSym (complexTrans (A.addCCongruent (C.≈C-refl _) (RealPoly.realMul (Shift.Kq ⋆) (b ⋆)))
      (RealPoly.realAdd (a ⋆) ((Shift.Kq ⋆) R.* (b ⋆))))))

stepRead : ∀ z c cs → asc z (Shift.step c cs) ≈C (realC (c ⋆) +C (K +C z) *C asc z cs)
stepRead z c [] =
  complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero z))
    (A.addCCongruent (C.≈C-refl _) (complexSym (L.complexMultiplyRightZero (K +C z))))
stepRead z c (a ∷ as) =
  let k = realC (c ⋆); v = realC (a ⋆); t = asc z as
  in complexTrans (A.addCCongruent (ratRead c a) (A.mulCCongruent (C.≈C-refl _) (stepRead z a as)))
    (complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyDistributesLeft z v ((K +C z) *C t)))
      (complexTrans (L.complexAddAssociative k (K *C v) ((z *C v) +C z *C ((K +C z) *C t)))
        (complexTrans (A.addCCongruent (C.≈C-refl _)
          (complexTrans (complexSym (L.complexAddAssociative (K *C v) (z *C v) (z *C ((K +C z) *C t))))
            (A.addCCongruent (complexSym (L.complexMultiplyDistributesRight K z v))
              (complexTrans (complexSym (L.complexMultiplyAssociative z (K +C z) t))
                (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative z (K +C z)) (C.≈C-refl _))
                  (L.complexMultiplyAssociative (K +C z) z t))))))
          (A.addCCongruent (C.≈C-refl _) (complexSym (L.complexMultiplyDistributesLeft (K +C z) v (z *C t)))))))

shiftRead : ∀ z acc cs → asc z (Shift.shiftFrom acc cs) ≈C desc (K +C z) (asc z acc) cs
shiftRead z acc [] = C.≈C-refl _
shiftRead z acc (c ∷ cs) = complexTrans (shiftRead z (Shift.step c acc) cs)
  (descCong (C.≈C-refl _) (stepRead z c acc) cs)

literalShift : ∀ z cs → asc z (Shift.shift cs) ≈C Poly.poly (K +C z) cs
literalShift z cs = complexTrans (shiftRead z [] cs) (descZero (K +C z) cs)

zeroCoeff : ∀ c → c Q.≃ 0ℚᵘ → realC (c ⋆) ≈C A.zeroC
zeroCoeff c h = P.⋆-cong h , P.≃-refl

doubleZero : ∀ z cs → Shift.head cs Q.≃ 0ℚᵘ → Shift.head (Shift.tail cs) Q.≃ 0ℚᵘ →
  asc z cs ≈C (powC z 2 *C asc z (Shift.drop 2 cs))
doubleZero z [] h k = complexSym (L.complexMultiplyRightZero _)
doubleZero z (c ∷ []) h k =
  complexTrans (A.addCCongruent (zeroCoeff c h) (L.complexMultiplyRightZero z))
    (complexTrans (L.complexAddLeftIdentity A.zeroC) (complexSym (L.complexMultiplyRightZero _)))
doubleZero z (c ∷ d ∷ cs) h k =
  complexTrans (A.addCCongruent (zeroCoeff c h) (A.mulCCongruent (C.≈C-refl _)
    (complexTrans (A.addCCongruent (zeroCoeff d k) (C.≈C-refl _)) (L.complexAddLeftIdentity _))))
    (complexTrans (L.complexAddLeftIdentity _) (complexTrans (complexSym (L.complexMultiplyAssociative z z (asc z cs)))
      (A.mulCCongruent (Power.powTwo z) (C.≈C-refl _))))

pComplement sComplement : BishopComplex → BishopComplex
pComplement z = asc z (Shift.drop 2 (Shift.shift Packet.diagonal))
sComplement z = asc z (Shift.drop 2 (Shift.shift Packet.slice))

center : ∀ j → (K +C (j -C K)) ≈C j
center j =
  (let open P.ℝ-Solver in solve 2 (λ k x → k ⊕ (x ⊖ k) ⊜ x) P.≃-refl (C.re K) (C.re j)) ,
  (let open P.ℝ-Solver in solve 2 (λ k x → k ⊕ (x ⊖ k) ⊜ x) P.≃-refl (C.im K) (C.im j))

diagonalFactor : ∀ j → Poly.poly j Packet.diagonal ≈C (powC (j -C K) 2 *C pComplement (j -C K))
diagonalFactor j = complexTrans (Poly.polyCong (complexSym (center j)) Packet.diagonal)
  (complexTrans (complexSym (literalShift (j -C K) Packet.diagonal))
    (doubleZero (j -C K) (Shift.shift Packet.diagonal) Shift.pZero Shift.pLinearZero))

sliceFactor : ∀ j → Poly.poly j Packet.slice ≈C (powC (j -C K) 2 *C sComplement (j -C K))
sliceFactor j = complexTrans (Poly.polyCong (complexSym (center j)) Packet.slice)
  (complexTrans (complexSym (literalShift (j -C K) Packet.slice))
    (doubleZero (j -C K) (Shift.shift Packet.slice) Shift.sZero Shift.sLinearZero))
