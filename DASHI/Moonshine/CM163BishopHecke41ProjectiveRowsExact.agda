module DASHI.Moonshine.CM163BishopHecke41ProjectiveRowsExact where

-- Source-written, kernel pending. Homogeneous row evaluation on the
-- original Bishop upper half-plane, without an arbitrary Möbius
-- quotient constructor. Every nonzero scale is retained.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base as Z using (ℤ; +_)
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.CM163ClassicalHecke41LatticeSpecializationExact as B
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Moonshine.CM163Hecke41CorrectionWordsExact as W
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC)
open Comp using (complexTrans; complexSym)

intMul : ∀ a b → K.embedInteger (a Z.* b) ≃ K.embedInteger a * K.embedInteger b
intMul a b = P.≃-trans (G.intRead (a Z.* b))
  (P.≃-trans (P.⋆-cong (Q.*≡*
    (let open +-*-Solver in solve 2 (λ a b →
      (a :* b) :* (Κ (+ 1) :* Κ (+ 1)) := (a :* b) :* Κ (+ 1)) refl a b)))
    (P.≃-trans (P.⋆-distrib-* (a / 1) (b / 1))
      (P.*-cong (P.≃-symm (G.intRead a)) (P.≃-symm (G.intRead b)))))

-- Use a normal form for the imaginary zero term. The read law attaches
-- it to the source-owned literal lattice denominator.
eval : L.LatticePoint → BishopComplex → BishopComplex
eval (L.lattice-point m n) (C.complex x y) =
  C.complex (K.embedInteger m * x + K.embedInteger n) (K.embedInteger m * y)

denomRead : ∀ r z → K.latticeDenominator r z ≈C eval r z
denomRead (L.lattice-point m n) (C.complex x y) =
  P.≃-refl , P.+-identityʳ (K.embedInteger m * y)

evalCong : ∀ r {z w} → z ≈C w → eval r z ≈C eval r w
evalCong (L.lattice-point m n) (x , y) =
  P.+-cong (P.*-congˡ x) P.≃-refl , P.*-congˡ y

evalAdd : ∀ u v z → eval (B.add u v) z ≈C (eval u z +C eval v z)
evalAdd (L.lattice-point m n) (L.lattice-point a b) (C.complex x y) =
  P.≃-trans (P.+-cong (P.*-congʳ (G.intAdd m a)) (G.intAdd n b))
    (let open P.ℝ-Solver in solve 5 (λ m n a b x →
      (m ⊕ a) ⊗ x ⊕ (n ⊕ b) ⊜ (m ⊗ x ⊕ n) ⊕ (a ⊗ x ⊕ b))
      P.≃-refl (K.embedInteger m) (K.embedInteger n) (K.embedInteger a) (K.embedInteger b) x) ,
  P.≃-trans (P.*-congʳ (G.intAdd m a))
    (let open P.ℝ-Solver in solve 3 (λ m a y → (m ⊕ a) ⊗ y ⊜ m ⊗ y ⊕ a ⊗ y)
      P.≃-refl (K.embedInteger m) (K.embedInteger a) y)

evalScale : ∀ k u z → eval (B.scale k u) z ≈C scaleC (K.embedInteger k) (eval u z)
evalScale k (L.lattice-point m n) (C.complex x y) =
  P.≃-trans (P.+-cong (P.*-congʳ (intMul k m)) (intMul k n))
    (let open P.ℝ-Solver in solve 4 (λ k m n x → (k ⊗ m) ⊗ x ⊕ k ⊗ n ⊜ k ⊗ (m ⊗ x ⊕ n))
      P.≃-refl (K.embedInteger k) (K.embedInteger m) (K.embedInteger n) x) ,
  P.≃-trans (P.*-congʳ (intMul k m)) (P.*-assoc _ _ y)

-- A row evaluated after an exact projective change of frame.
linearFactor : ∀ a b f z →
  (scaleC (K.embedInteger a) (f *C z) +C scaleC (K.embedInteger b) f) ≈C
  (f *C eval (L.lattice-point a b) z)
linearFactor a b (C.complex f g) (C.complex x y) =
  (let open P.ℝ-Solver in solve 6 (λ a b f g x y →
    a ⊗ (f ⊗ x ⊖ g ⊗ y) ⊕ b ⊗ f
    ⊜ f ⊗ (a ⊗ x ⊕ b) ⊖ g ⊗ (a ⊗ y))
    P.≃-refl (K.embedInteger a) (K.embedInteger b) f g x y) ,
  (let open P.ℝ-Solver in solve 6 (λ a b f g x y →
    a ⊗ (f ⊗ y ⊕ g ⊗ x) ⊕ b ⊗ g
    ⊜ f ⊗ (a ⊗ y) ⊕ g ⊗ (a ⊗ x ⊕ b))
    P.≃-refl (K.embedInteger a) (K.embedInteger b) f g x y)

rowCompose : ∀ a b u v z f w →
  eval u z ≈C (f *C w) → eval v z ≈C f →
  eval (B.add (B.scale a u) (B.scale b v)) z ≈C
  (f *C eval (L.lattice-point a b) w)
rowCompose a b u v z f w hu hv =
  complexTrans (evalAdd (B.scale a u) (B.scale b v) z)
    (complexTrans (A.addCCongruent (evalScale a u z) (evalScale b v z))
      (complexTrans (A.addCCongruent (A.scaleCCongruent hu _) (A.scaleCCongruent hv _))
        (linearFactor a b f w)))

record Read (r : B.Rows) (p q : U.BishopUpperHalfPlanePoint) : Set where
  constructor read
  field
    factor : BishopComplex
    factorNZ : Rec.BishopComplexNonzero factor
    upper : eval (B.first r) (U.tau p) ≈C (factor *C U.tau q)
    lower : eval (B.second r) (U.tau p) ≈C factor
open Read public

compose : ∀ a b p q v → Read b p q → Read a q v → Read (H.mul a b) p v
compose (B.rows (L.lattice-point a b) (L.lattice-point c d)) r p q v h k =
  read (factor h *C factor k) (J.nonzeroMul (factorNZ h) (factorNZ k))
    (complexTrans (rowCompose a b (B.first r) (B.second r) (U.tau p) (factor h) (U.tau q) (upper h) (lower h))
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (upper k))
        (complexSym (Laws.complexMultiplyAssociative _ _ _))))
    (complexTrans (rowCompose c d (B.first r) (B.second r) (U.tau p) (factor h) (U.tau q) (upper h) (lower h))
      (A.mulCCongruent (C.≈C-refl _) (lower k)))

-- Comparing the literal upper/lower pair cancels its nonzero common
-- scale; this is not equality of upper-half-plane proof records.
samePoint : ∀ r p q v → Read r p q → Read r p v → U.tau q ≈C U.tau v
samePoint r p q v h k = J.cancelLeft (factor h) _ _ (factorNZ h)
  (complexTrans (complexSym (upper h))
    (complexTrans (upper k) (A.mulCCongruent
      (complexTrans (complexSym (lower k)) (lower h)) (C.≈C-refl _))))

oneRow : ∀ z → eval (L.lattice-point (+ 0) (+ 1)) z ≈C A.oneC
oneRow (C.complex x y) =
  (let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊕ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl x) ,
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊗ y ⊜ Κ 0ℚᵘ) P.≃-refl y)

tauRow : ∀ z → eval (L.lattice-point (+ 1) (+ 0)) z ≈C z
tauRow (C.complex x y) =
  (let open P.ℝ-Solver in solve 1 (λ x → Κ 1ℚᵘ ⊗ x ⊕ Κ 0ℚᵘ ⊜ x) P.≃-refl x) ,
  P.*-identityˡ y

minusRow : ∀ z → eval (L.lattice-point (+ 0) (Z.- (+ 1))) z ≈C G.minusOneC
minusRow (C.complex x y) =
  (let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊗ x ⊕ (⊝ Κ 1ℚᵘ) ⊜ ⊝ Κ 1ℚᵘ) P.≃-refl x) ,
  (let open P.ℝ-Solver in solve 1 (λ y → Κ 0ℚᵘ ⊗ y ⊜ Κ 0ℚᵘ) P.≃-refl y)

idRead : ∀ p → Read H.identityRows p p
idRead p = read A.oneC J.nonzeroOne
  (complexTrans (tauRow (U.tau p)) (complexSym (Laws.complexMultiplyLeftIdentity _)))
  (oneRow (U.tau p))

step : W.Step → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
step W.s = G.actS
step W.t = G.actT

stepRead : ∀ g p → Read (W.stepRows g) p (step g p)
stepRead W.s p = read (U.tau p) (G.tauNZ p)
  (complexTrans (minusRow (U.tau p)) (complexSym (G.tauTimesS p)))
  (tauRow (U.tau p))
stepRead W.t p = read A.oneC J.nonzeroOne
  (complexTrans
    ((let open P.ℝ-Solver in solve 1 (λ x → Κ 1ℚᵘ ⊗ x ⊕ Κ 1ℚᵘ ⊜ x ⊕ Κ 1ℚᵘ) P.≃-refl (C.re (U.tau p))) ,
     P.*-identityˡ (C.im (U.tau p)))
    (complexSym (Laws.complexMultiplyLeftIdentity _)))
  (oneRow (U.tau p))

word : W.Word → U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
word [] p = p
word (g ∷ gs) p = step g (word gs p)

wordRead : ∀ w p → Read (W.matrix w) p (word w p)
wordRead [] p = idRead p
wordRead (g ∷ gs) p = compose (W.stepRows g) (W.matrix gs) p (word gs p) (step g (word gs p))
  (wordRead gs p) (stepRead g (word gs p))
