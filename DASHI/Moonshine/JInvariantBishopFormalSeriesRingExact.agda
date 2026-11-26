module DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact where

-- SOURCE-WRITTEN, UNCOMPILED. Bundle the original Bishop Cauchy row,
-- not a new series type. Reuse the vendored Bishop rational-coefficient
-- solver (NonReflective) and the already-owned pointwise/row laws.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Product.Base using (_,_)
open import Data.Maybe.Base using (nothing)
open import Data.Bool.Base using (T)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _⋆)
import RealProperties as P
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR
open import Tactic.RingSolver.Core.Polynomial.Parameters using (Homomorphism)
import NonReflective
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
open U public using (Series; _⊕s_; _⊖s_; _⊗s_; scale)

infix 4 _≈s_
_≈s_ : Series → Series → Set
f ≈s g = ∀ n → f n ≃ g n

reflS : ∀ {f} → f ≈s f
reflS n = P.≃-refl
symS : ∀ {f g} → f ≈s g → g ≈s f
symS h n = P.≃-symm (h n)
transS : ∀ {f g h} → f ≈s g → g ≈s h → f ≈s h
transS p q n = P.≃-trans (p n) (q n)

neg : Series → Series
neg f n = R.- (f n)

addCong : ∀ {a b c d} → a ≈s b → c ≈s d → (a ⊕s c) ≈s (b ⊕s d)
addCong p q n = P.+-cong (p n) (q n)
negCong : ∀ {a b} → a ≈s b → neg a ≈s neg b
negCong h n = P.-‿cong (h n)
subCong : ∀ {a b c d} → a ≈s b → c ≈s d → (a ⊖s c) ≈s (b ⊖s d)
subCong p q = addCong p (negCong q)
mulCong : ∀ {a b c d} → a ≈s b → c ≈s d → (a ⊗s c) ≈s (b ⊗s d)
mulCong {a} {b} {c} {d} p q = W.rowCong a c b d p q

seriesRing : CommutativeRing _ _
seriesRing = record
  { Carrier = Series
  ; _≈_ = _≈s_
  ; _+_ = _⊕s_
  ; _*_ = _⊗s_
  ; -_ = neg
  ; 0# = H.zeroSeries
  ; 1# = H.unitSeries
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = record { refl = reflS ; sym = symS ; trans = transS }
                ; ∙-cong = addCong
                }
              ; assoc = λ a b c n → P.+-assoc (a n) (b n) (c n)
              }
            ; identity = (λ a n → P.+-identityˡ (a n)) , (λ a n → P.+-identityʳ (a n))
            }
          ; inverse = (λ a n → P.+-inverseˡ (a n)) , (λ a n → P.+-inverseʳ (a n))
          ; ⁻¹-cong = negCong
          }
        ; comm = λ a b n → P.+-comm (a n) (b n)
        }
      ; *-cong = mulCong
      ; *-assoc = W.rowAssoc
      ; *-identity = W.rowUnitLeft , W.rowUnitRight
      ; distrib = W.rowAddRight , (λ a b c → W.rowAddLeft b c a)
      }
    ; *-comm = W.rowComm
    }
  }

constant : ℝ → Series
constant a zero = a
constant a (suc n) = R.0ℝ

constantScale : (a : ℝ) (f : Series) → (constant a ⊗s f) ≈s scale a f
constantScale a f zero = C.cauchyCoefficientZero (constant a) f
constantScale a f (suc n) =
  P.≃-trans (C.cauchyCoefficientSuccessor (constant a) f n)
    (P.≃-trans (P.+-cong P.≃-refl (W.rowZeroLeft f n))
      (P.+-identityʳ (R._*_ a (f (suc n)))))

constantCong : ∀ {a b} → a ≃ b → constant a ≈s constant b
constantCong h zero = h
constantCong h (suc n) = P.≃-refl

constantAdd : (a b : ℝ) → constant (R._+_ a b) ≈s (constant a ⊕s constant b)
constantAdd a b zero = P.≃-refl
constantAdd a b (suc n) = P.≃-symm (P.+-identityʳ R.0ℝ)

constantMul : (a b : ℝ) → constant (R._*_ a b) ≈s (constant a ⊗s constant b)
constantMul a b zero = P.≃-symm (constantScale a (constant b) zero)
constantMul a b (suc n) = P.≃-trans (P.≃-symm (P.*-zeroʳ a))
  (P.≃-symm (constantScale a (constant b) (suc n)))

constantNeg : (a : ℝ) → constant (R.- a) ≈s neg (constant a)
constantNeg a zero = P.≃-refl
constantNeg a (suc n) = P.≃-symm P.0≃-0

solverRing : ACR.AlmostCommutativeRing _ _
solverRing = ACR.fromCommutativeRing seriesRing (λ _ → nothing)

rat : ℚᵘ → Series
rat a = constant (a ⋆)

morphism : ACR._-Raw-AlmostCommutative⟶_ QP.+-*-rawRing solverRing
morphism = record
  { ⟦_⟧ = rat
  ; +-homo = λ a b → transS (constantCong (P.⋆-distrib-+ a b)) (constantAdd (a ⋆) (b ⋆))
  ; *-homo = λ a b → transS (constantCong (P.⋆-distrib-* a b)) (constantMul (a ⋆) (b ⋆))
  ; -‿homo = λ a → transS (constantCong (P.⋆-distrib-neg a)) (constantNeg (a ⋆))
  ; 0-homo = reflS
  ; 1-homo = reflS
  }

zeroCheck : ∀ p → T (P.ℝ-Solver.ℚ-isZero p) → H.zeroSeries ≈s rat p
zeroCheck p h = constantCong (P.ℝ-Solver.zero-checker p h)

homo : Homomorphism _ _ _ _
homo = record
  { from = P.ℝ-Solver.ℚ-coeff
  ; to = solverRing
  ; morphism = morphism
  ; Zero-C⟶Zero-R = zeroCheck
  }

module Solver where
  open NonReflective homo public
  open import Tactic.RingSolver.Core.Expression public

scaleIsProduct : (a : ℚᵘ) (f : Series) → scale (a ⋆) f ≈s (rat a ⊗s f)
scaleIsProduct a f = symS (constantScale (a ⋆) f)
