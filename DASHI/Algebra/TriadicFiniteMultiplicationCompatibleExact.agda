module DASHI.Algebra.TriadicFiniteMultiplicationCompatibleExact where

-- Extend the ORIGINAL finite balanced-ternary arithmetic by multiplication
-- via low-first Horner recursion, with existing carry-aware addition.
-- The result is compatible with the native inverse-limit projections.
-- Ring laws, valuation and field-of-fractions are separate obligations.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; []; _∷_)
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as A

reduceZero : ∀ n → Q.reduce (A.zeroResidue (suc n)) ≡ A.zeroResidue n
reduceZero zero = refl
reduceZero (suc n) rewrite reduceZero n = refl

reduceNeg : ∀ {n} (x : Q.Residue3Pow (suc n)) →
  Q.reduce (A.negateResidue x) ≡ A.negateResidue (Q.reduce x)
reduceNeg {zero} (x ∷ []) = refl
reduceNeg {suc n} (x ∷ xs) rewrite reduceNeg {n} xs = refl

scaleTrit : ∀ {n} → Trit → Q.Residue3Pow n → Q.Residue3Pow n
scaleTrit neg x = A.negateResidue x
scaleTrit {n} zer x = A.zeroResidue n
scaleTrit pos x = x

reduceScale : ∀ {n} (d : Trit) (x : Q.Residue3Pow (suc n)) →
  Q.reduce (scaleTrit d x) ≡ scaleTrit d (Q.reduce x)
reduceScale neg x = reduceNeg x
reduceScale {n} zer x = reduceZero n
reduceScale pos x = refl

multiply : ∀ {n} → Q.Residue3Pow n → Q.Residue3Pow n → Q.Residue3Pow n
multiply [] [] = []
multiply (d ∷ ds) (e ∷ es) =
  A.addResidue (scaleTrit d (e ∷ es))
    (zer ∷ multiply ds (Q.reduce (e ∷ es)))

reduceMultiply : ∀ {n} (x y : Q.Residue3Pow (suc n)) →
  Q.reduce (multiply x y) ≡ multiply (Q.reduce x) (Q.reduce y)
reduceMultiply {zero} (d ∷ []) (e ∷ []) =
  trans (A.reduce-addResidue (scaleTrit d (e ∷ [])) (zer ∷ []))
    (cong₂ A.addResidue (reduceScale d (e ∷ [])) refl)
reduceMultiply {suc n} (d ∷ ds) (e ∷ ytail) =
  trans (A.reduce-addResidue (scaleTrit d (e ∷ ytail))
          (zer ∷ multiply ds (Q.reduce (e ∷ ytail))))
    (cong₂ A.addResidue (reduceScale d (e ∷ ytail))
      (cong (zer ∷_) (reduceMultiply {n} ds (Q.reduce (e ∷ ytail)))))

-- Construct the operations on the existing compatible tower. No new
-- completion carrier and no pointwise function extensionality assumption.
addLimit : Q.TriadicInverseLimitPoint → Q.TriadicInverseLimitPoint →
  Q.TriadicInverseLimitPoint
addLimit x y = Q.triadic-limit-point
  (λ n → A.addResidue (Q.coordinate x n) (Q.coordinate y n))
  (λ n → trans (A.reduce-addResidue (Q.coordinate x (suc n)) (Q.coordinate y (suc n)))
    (cong₂ A.addResidue (Q.compatible x n) (Q.compatible y n)))

negateLimit : Q.TriadicInverseLimitPoint → Q.TriadicInverseLimitPoint
negateLimit x = Q.triadic-limit-point
  (λ n → A.negateResidue (Q.coordinate x n))
  (λ n → trans (reduceNeg (Q.coordinate x (suc n)))
    (cong A.negateResidue (Q.compatible x n)))

multiplyLimit : Q.TriadicInverseLimitPoint → Q.TriadicInverseLimitPoint →
  Q.TriadicInverseLimitPoint
multiplyLimit x y = Q.triadic-limit-point
  (λ n → multiply (Q.coordinate x n) (Q.coordinate y n))
  (λ n → trans (reduceMultiply (Q.coordinate x (suc n)) (Q.coordinate y (suc n)))
    (cong₂ multiply (Q.compatible x n) (Q.compatible y n)))
