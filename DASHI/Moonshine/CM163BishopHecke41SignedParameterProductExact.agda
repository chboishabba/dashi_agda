module DASHI.Moonshine.CM163BishopHecke41SignedParameterProductExact where

-- SOURCE-WRITTEN, kernel pending. Preserve BOTH reflection sectors.
-- Polynomial parameter Y is real; the Hecke coefficients stay Bishop
-- complex. Pair evaluated at Z=Y^2 is the even and odd coefficient fibre.
-- The original Fin-fold product is recovered at +Y AND -Y.
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Fin as Fin using (Fin)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _*_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

Pair : Set
Pair = BishopComplex × BishopComplex

positive negative : ℝ → Pair → BishopComplex
positive y (e , o) = e +C scaleC y o
negative y (e , o) = e -C scaleC y o

multiply : ℝ → Pair → Pair → Pair
multiply z (e , o) (f , p) =
  (e *C f +C scaleC z (o *C p)) , (e *C p +C o *C f)

mulPositive : ∀ y p q → positive y (multiply (y * y) p q) ≈C
  (positive y p *C positive y q)
mulPositive y (C.complex a b , C.complex c d) (C.complex g h , C.complex i j) =
  (let open P.ℝ-Solver in solve 9 (λ y a b c d g h i j → ((((a ⊗ g) ⊖ (b ⊗ h)) ⊕ ((y ⊗ y) ⊗ ((c ⊗ i) ⊖ (d ⊗ j)))) ⊕ (y ⊗ (((a ⊗ i) ⊖ (b ⊗ j)) ⊕ ((c ⊗ g) ⊖ (d ⊗ h))))) ⊜ (((a ⊕ (y ⊗ c)) ⊗ (g ⊕ (y ⊗ i))) ⊖ ((b ⊕ (y ⊗ d)) ⊗ (h ⊕ (y ⊗ j))))) P.≃-refl y a b c d g h i j) ,
  (let open P.ℝ-Solver in solve 9 (λ y a b c d g h i j → ((((a ⊗ h) ⊕ (b ⊗ g)) ⊕ ((y ⊗ y) ⊗ ((c ⊗ j) ⊕ (d ⊗ i)))) ⊕ (y ⊗ (((a ⊗ j) ⊕ (b ⊗ i)) ⊕ ((c ⊗ h) ⊕ (d ⊗ g))))) ⊜ (((a ⊕ (y ⊗ c)) ⊗ (h ⊕ (y ⊗ j))) ⊕ ((b ⊕ (y ⊗ d)) ⊗ (g ⊕ (y ⊗ i))))) P.≃-refl y a b c d g h i j)

mulNegative : ∀ y p q → negative y (multiply (y * y) p q) ≈C
  (negative y p *C negative y q)
mulNegative y (C.complex a b , C.complex c d) (C.complex g h , C.complex i j) =
  (let open P.ℝ-Solver in solve 9 (λ y a b c d g h i j → ((((a ⊗ g) ⊖ (b ⊗ h)) ⊕ ((y ⊗ y) ⊗ ((c ⊗ i) ⊖ (d ⊗ j)))) ⊖ (y ⊗ (((a ⊗ i) ⊖ (b ⊗ j)) ⊕ ((c ⊗ g) ⊖ (d ⊗ h))))) ⊜ (((a ⊖ (y ⊗ c)) ⊗ (g ⊖ (y ⊗ i))) ⊖ ((b ⊖ (y ⊗ d)) ⊗ (h ⊖ (y ⊗ j))))) P.≃-refl y a b c d g h i j) ,
  (let open P.ℝ-Solver in solve 9 (λ y a b c d g h i j → ((((a ⊗ h) ⊕ (b ⊗ g)) ⊕ ((y ⊗ y) ⊗ ((c ⊗ j) ⊕ (d ⊗ i)))) ⊖ (y ⊗ (((a ⊗ j) ⊕ (b ⊗ i)) ⊕ ((c ⊗ h) ⊕ (d ⊗ g))))) ⊜ (((a ⊖ (y ⊗ c)) ⊗ (h ⊖ (y ⊗ j))) ⊕ ((b ⊖ (y ⊗ d)) ⊗ (g ⊖ (y ⊗ i))))) P.≃-refl y a b c d g h i j)

one : Pair
one = A.oneC , A.zeroC

factor : BishopComplex → Pair
factor j = (A.zeroC -C j) , A.oneC

positiveOne : ∀ y → positive y one ≈C A.oneC
positiveOne y =
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 1ℚᵘ ⊕ y ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl y) ,
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊕ y ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl y)

negativeOne : ∀ y → negative y one ≈C A.oneC
negativeOne y =
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 1ℚᵘ ⊖ y ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl y) ,
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊖ y ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl y)

positiveFactor : ∀ y j → positive y (factor j) ≈C (C.complex y R.0ℝ -C j)
positiveFactor y (C.complex a b) =
  (let open P.ℝ-Solver in solve 2 (λ y a → (Κ 0ℚᵘ ⊖ a) ⊕ y ⊗ Κ 1ℚᵘ ⊜ y ⊖ a) P.≃-refl y a) ,
  (let open P.ℝ-Solver in solve 2 (λ y b → (Κ 0ℚᵘ ⊖ b) ⊕ y ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊖ b) P.≃-refl y b)

negativeFactor : ∀ y j → negative y (factor j) ≈C (C.complex (R.- y) R.0ℝ -C j)
negativeFactor y (C.complex a b) =
  (let open P.ℝ-Solver in solve 2 (λ y a → (Κ 0ℚᵘ ⊖ a) ⊖ y ⊗ Κ 1ℚᵘ ⊜ (⊝ y) ⊖ a) P.≃-refl y a) ,
  (let open P.ℝ-Solver in solve 2 (λ y b → (Κ 0ℚᵘ ⊖ b) ⊖ y ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊖ b) P.≃-refl y b)

fold : ∀ {n} → ℝ → (Fin n → BishopComplex) → Pair
fold {zero} z f = one
fold {suc n} z f = multiply z (factor (f Fin.zero)) (fold z (λ i → f (Fin.suc i)))

foldPositive : ∀ {n} y (f : Fin n → BishopComplex) →
  positive y (fold (y * y) f) ≈C Prod.product (λ i → C.complex y R.0ℝ -C f i)
foldPositive {zero} y f = positiveOne y
foldPositive {suc n} y f = complexTrans (mulPositive y _ _)
  (A.mulCCongruent (positiveFactor y (f Fin.zero)) (foldPositive y (λ i → f (Fin.suc i))))

foldNegative : ∀ {n} y (f : Fin n → BishopComplex) →
  negative y (fold (y * y) f) ≈C Prod.product (λ i → C.complex (R.- y) R.0ℝ -C f i)
foldNegative {zero} y f = negativeOne y
foldNegative {suc n} y f = complexTrans (mulNegative y _ _)
  (A.mulCCongruent (negativeFactor y (f Fin.zero)) (foldNegative y (λ i → f (Fin.suc i))))

-- Cleared readback: don't throw away the odd coordinate and don't
-- divide by Y at the origin. At nonzero nodes the two reads determine
-- both coordinates; the origin consumes the even read alone.
readSum : ∀ y e o → (positive y (e , o) +C negative y (e , o)) ≈C (e +C e)
readSum y (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 3 (λ y a c → (a ⊕ y ⊗ c) ⊕ (a ⊖ y ⊗ c) ⊜ a ⊕ a) P.≃-refl y a c) ,
  (let open P.ℝ-Solver in solve 3 (λ y b d → (b ⊕ y ⊗ d) ⊕ (b ⊖ y ⊗ d) ⊜ b ⊕ b) P.≃-refl y b d)

readDifference : ∀ y e o → (positive y (e , o) -C negative y (e , o)) ≈C
  (scaleC y o +C scaleC y o)
readDifference y (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 3 (λ y a c → (a ⊕ y ⊗ c) ⊖ (a ⊖ y ⊗ c) ⊜ y ⊗ c ⊕ y ⊗ c) P.≃-refl y a c) ,
  (let open P.ℝ-Solver in solve 3 (λ y b d → (b ⊕ y ⊗ d) ⊖ (b ⊖ y ⊗ d) ⊜ y ⊗ d ⊕ y ⊗ d) P.≃-refl y b d)
