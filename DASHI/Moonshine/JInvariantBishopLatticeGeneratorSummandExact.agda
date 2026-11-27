module DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact where

-- The actual Möbius generator actions on the original Bishop upper
-- half plane, and the literal reciprocal-power summand transformations.
-- Positivity and inverse uniqueness are proved, not assumed.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong₂; subst)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
open A using (_*C_; _+C_)
open C using (_≈C_)
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open Comp using (complexTrans; complexSym)
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Rot
import DASHI.Moonshine.JInvariantBishopShearExhaustionExact as Shear
import DASHI.Moonshine.CM163ClassicalHecke41GeneratorTransportExact as H
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L

intRead : (z : ℤ) → K.embedInteger z ≃ ((z / 1) ⋆)
intRead (+ n) = P.≃-refl
intRead (-[1+ n ]) = P.≃-symm (P.⋆-distrib-neg (+ suc n / 1))

intAdd : (a b : ℤ) → K.embedInteger (a Z.+ b) ≃ (K.embedInteger a + K.embedInteger b)
intAdd a b = P.≃-trans (intRead (a Z.+ b))
  (P.≃-trans (P.⋆-cong (Q.*≡*
    (let open +-*-Solver in solve 2 (λ a b →
      (a :+ b) :* Κ (+ 1) := (a :* Κ (+ 1) :+ b :* Κ (+ 1)) :* Κ (+ 1)) refl a b)))
    (P.≃-trans (P.⋆-distrib-+ (a / 1) (b / 1))
      (P.+-cong (P.≃-symm (intRead a)) (P.≃-symm (intRead b)))))

intNeg : (a : ℤ) → K.embedInteger (Z.- a) ≃ R.- (K.embedInteger a)
intNeg a = P.≃-trans (intRead (Z.- a))
  (P.≃-trans (P.⋆-distrib-neg (a / 1)) (P.-‿cong (P.≃-symm (intRead a))))

negC : C.BishopComplex → C.BishopComplex
negC z = C.complex (R.- (C.re z)) (R.- (C.im z))

minusOneC : C.BishopComplex
minusOneC = C.complex (R.- R.1ℝ) R.0ℝ

tauNZ : (p : U.BishopUpperHalfPlanePoint) → Rec.BishopComplexNonzero (U.tau p)
tauNZ p = NZ.complexNonzeroFromImagApart (inj₂ (U.imaginaryPositive p))

actT : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
actT p = U.bishop-upper-half-plane-point
  (C.complex (C.re (U.tau p) + R.1ℝ) (C.im (U.tau p))) (U.imaginaryPositive p)

actS : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint
actS p = U.bishop-upper-half-plane-point (negC (Rec.reciprocalC (U.tau p) (tauNZ p))) positive
  where
  d = Norm.normSqC (U.tau p)
  nz = Rec.normSquareNonzero (tauNZ p)
  inv = I._⁻¹ d nz
  y = C.im (U.tau p)
  positive : R._<_ R.0ℝ (R.- (inv * R.- y))
  positive = P.<-respʳ-≃
    (let open P.ℝ-Solver in solve 2 (λ i y → i ⊗ y ⊜ ⊝ (i ⊗ (⊝ y))) P.≃-refl inv y)
    (P.posx⇒0<x (P.posx,y⇒posx*y
      (P.0<x⇒posx (I.0<x⇒0<x⁻¹ nz (Rec.normSquarePositive (tauNZ p))))
      (P.0<x⇒posx (U.imaginaryPositive p))))

tauTimesS : ∀ p → (U.tau p *C U.tau (actS p)) ≈C minusOneC
tauTimesS p =
  let z = U.tau p
      v = Rec.reciprocalC z (tauNZ p)
      h = Rec.multiplyReciprocal z (tauNZ p)
      x = C.re z
      y = C.im z
      a = C.re v
      b = C.im v
      open P.ℝ-Solver
  in P.≃-trans
       (solve 4 (λ x y a b → x ⊗ (⊝ a) ⊖ y ⊗ (⊝ b) ⊜ ⊝ (x ⊗ a ⊖ y ⊗ b))
        P.≃-refl x y a b) (P.-‿cong (proj₁ h)) ,
     P.≃-trans
       (solve 4 (λ x y a b → x ⊗ (⊝ b) ⊕ y ⊗ (⊝ a) ⊜ ⊝ (x ⊗ b ⊕ y ⊗ a))
        P.≃-refl x y a b)
       (P.≃-trans (P.-‿cong (proj₂ h))
         (solve 0 (⊝ Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl))

denomT : ∀ p i →
  K.latticeDenominator (K.point i) (U.tau (actT p)) ≈C
  K.latticeDenominator (K.point (Re.forwardPunctured H.T i)) (U.tau p)
denomT p i =
  let q = K.point i
      m = K.embedInteger (L.horizontal q)
      n = K.embedInteger (L.vertical q)
      z = U.tau p
      x = C.re z
      y = C.im z
      open P.ℝ-Solver
      law : K.latticeDenominator q (U.tau (actT p)) ≈C
        K.latticeDenominator (Shear.shear q) z
      law = P.≃-trans (solve 3 (λ m n x → m ⊗ (x ⊕ Κ Q.1ℚᵘ) ⊕ n ⊜ m ⊗ x ⊕ (m ⊕ n))
        P.≃-refl m n x)
        (P.+-cong P.≃-refl (P.≃-symm (intAdd (L.horizontal q) (L.vertical q)))) ,
        P.≃-refl
  in subst (λ k → K.latticeDenominator q (U.tau (actT p)) ≈C K.latticeDenominator k z)
    (sym (Shear.shearIsGenerator q)) law

denomS : ∀ p i →
  (U.tau p *C K.latticeDenominator (K.point i) (U.tau (actS p))) ≈C
  K.latticeDenominator (K.point (Re.forwardPunctured H.S i)) (U.tau p)
denomS p i =
  let q = K.point i
      m = K.embedInteger (L.horizontal q)
      n = K.embedInteger (L.vertical q)
      z = U.tau p
      w = U.tau (actS p)
      x = C.re z
      y = C.im z
      u = C.re w
      v = C.im w
      h = tauTimesS p
      open P.ℝ-Solver
      law : (z *C K.latticeDenominator q w) ≈C K.latticeDenominator (Rot.rot q) z
      law =
        P.≃-trans (solve 6 (λ m n x y u v →
          x ⊗ (m ⊗ u ⊕ n) ⊖ y ⊗ (m ⊗ v ⊕ Κ Q.0ℚᵘ)
          ⊜ n ⊗ x ⊕ m ⊗ (x ⊗ u ⊖ y ⊗ v)) P.≃-refl m n x y u v)
          (P.≃-trans (P.+-cong P.≃-refl (P.*-congˡ (proj₁ h)))
            (P.≃-trans (solve 3 (λ m n x → n ⊗ x ⊕ m ⊗ (⊝ Κ Q.1ℚᵘ) ⊜ n ⊗ x ⊕ (⊝ m))
              P.≃-refl m n x)
              (P.+-cong P.≃-refl (P.≃-symm (intNeg (L.horizontal q)))))) ,
        P.≃-trans (solve 6 (λ m n x y u v →
          x ⊗ (m ⊗ v ⊕ Κ Q.0ℚᵘ) ⊕ y ⊗ (m ⊗ u ⊕ n)
          ⊜ n ⊗ y ⊕ m ⊗ (x ⊗ v ⊕ y ⊗ u)) P.≃-refl m n x y u v)
          (P.≃-trans (P.+-cong P.≃-refl (P.*-congˡ (proj₂ h)))
            (solve 3 (λ n y m → n ⊗ y ⊕ m ⊗ Κ Q.0ℚᵘ ⊜ n ⊗ y ⊕ Κ Q.0ℚᵘ)
              P.≃-refl n y m))
  in subst (λ k → (z *C K.latticeDenominator q w) ≈C K.latticeDenominator k z)
    (sym (Rot.rotIsGenerator q)) law

-- Use the already-proved complex commutative semiring and inverse law.
-- The proof does not divide by a summand or introduce an analytic axiom.
reciprocalUnique : ∀ z nz v → (z *C v) ≈C A.oneC → Rec.reciprocalC z nz ≈C v
reciprocalUnique z nz v h =
  let u = Rec.reciprocalC z nz in
  complexTrans (complexSym (Laws.complexMultiplyRightIdentity u))
    (complexTrans (A.mulCCongruent (C.≈C-refl u) (complexSym h))
      (complexTrans (complexSym (Laws.complexMultiplyAssociative u z v))
        (complexTrans (A.mulCCongruent
          (complexTrans (Laws.complexMultiplyCommutative u z) (Rec.multiplyReciprocal z nz))
          (C.≈C-refl v))
          (Laws.complexMultiplyLeftIdentity v))))

reciprocalCong : ∀ z w nz nw → z ≈C w → Rec.reciprocalC z nz ≈C Rec.reciprocalC w nw
reciprocalCong z w nz nw eq = reciprocalUnique z nz (Rec.reciprocalC w nw)
  (complexTrans (A.mulCCongruent eq (C.≈C-refl (Rec.reciprocalC w nw))) (Rec.multiplyReciprocal w nw))

-- Commutative four-factor reassociation, with the existing semiring laws.
shuffle : ∀ a b c d → ((a *C b) *C (c *C d)) ≈C ((a *C c) *C (b *C d))
shuffle a b c d = complexTrans (Laws.complexMultiplyAssociative a b (c *C d))
  (complexTrans (A.mulCCongruent (C.≈C-refl a)
    (complexTrans (complexSym (Laws.complexMultiplyAssociative b c d))
      (complexTrans (A.mulCCongruent (Laws.complexMultiplyCommutative b c) (C.≈C-refl d))
        (Laws.complexMultiplyAssociative c b d))))
    (complexSym (Laws.complexMultiplyAssociative a c (b *C d))))

powProduct : ∀ a b k → A.powC (a *C b) k ≈C (A.powC a k *C A.powC b k)
powProduct a b zero = complexSym (Laws.complexMultiplyLeftIdentity A.oneC)
powProduct a b (suc k) = complexTrans (A.mulCCongruent (C.≈C-refl (a *C b)) (powProduct a b k))
  (shuffle a b (A.powC a k) (A.powC b k))

summandT : ∀ k p i →
  E.summand k (actT p) i ≈C E.summand k p (Re.forwardPunctured H.T i)
summandT k p i = A.powCCongruent
  (reciprocalCong (K.latticeDenominator (K.point i) (U.tau (actT p)))
    (K.latticeDenominator (K.point (Re.forwardPunctured H.T i)) (U.tau p))
    (U.upperHalfPlaneDenominatorNonzero (actT p) i)
    (U.upperHalfPlaneDenominatorNonzero p (Re.forwardPunctured H.T i)) (denomT p i)) k

summandS : ∀ k p i →
  E.summand k (actS p) i ≈C (A.powC (U.tau p) k *C E.summand k p (Re.forwardPunctured H.S i))
summandS k p i =
  let z = U.tau p
      d = K.latticeDenominator (K.point i) (U.tau (actS p))
      j = Re.forwardPunctured H.S i
      e = K.latticeDenominator (K.point j) z
      dn = U.upperHalfPlaneDenominatorNonzero (actS p) i
      en = U.upperHalfPlaneDenominatorNonzero p j
      v = Rec.reciprocalC e en
      cancels : (d *C (z *C v)) ≈C A.oneC
      cancels = complexTrans (complexSym (Laws.complexMultiplyAssociative d z v))
        (complexTrans (A.mulCCongruent
          (complexTrans (Laws.complexMultiplyCommutative d z) (denomS p i))
          (C.≈C-refl v))
          (Rec.multiplyReciprocal e en))
  in complexTrans (A.powCCongruent (reciprocalUnique d dn (z *C v) cancels) k)
    (powProduct z v k)
