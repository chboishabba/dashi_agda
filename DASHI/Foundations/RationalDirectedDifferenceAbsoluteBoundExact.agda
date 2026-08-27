module DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact where

------------------------------------------------------------------------
-- DIRECTED ERROR BOUNDS -> ABSOLUTE ERROR BOUND
--
-- In any use below all arithmetic is the standard-library unnormalised
-- rational arithmetic used by the pinned Bishop Real carrier.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _+_; _-_; -_; _≤_; _≃_; ∣_∣; NonNegative)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel

differenceUpperFromRight :
  ∀ {x y leftError rightError : ℚᵘ} →
  .{{_ : NonNegative leftError}} →
  x ℚ.≤ y ℚ.+ rightError →
  (x ℚ.- y) ℚ.≤ leftError ℚ.+ rightError
differenceUpperFromRight {x} {y} {leftError} {rightError} x≤y+r =
  let open ℚP.≤-Reasoning in
  begin
    x ℚ.- y
      ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- y) x≤y+r ⟩
    (y ℚ.+ rightError) ℚ.- y
      ≃⟨ ℚP.+-assoc y rightError (ℚ.- y) ⟩
    y ℚ.+ (rightError ℚ.- y)
      ≃⟨ ℚP.+-congʳ y (ℚP.+-comm rightError (ℚ.- y)) ⟩
    y ℚ.+ ((ℚ.- y) ℚ.+ rightError)
      ≃⟨ ℚP.≃-sym (ℚP.+-assoc y (ℚ.- y) rightError) ⟩
    (y ℚ.- y) ℚ.+ rightError
      ≃⟨ ℚP.+-congˡ rightError (ℚP.+-inverseʳ y) ⟩
    ℚ.0ℚᵘ ℚ.+ rightError
      ≃⟨ ℚP.+-identityˡ rightError ⟩
    rightError
      ≤⟨ ℚP.p≤q+p rightError leftError ⟩
    leftError ℚ.+ rightError
  ∎

differenceUpperFromLeft :
  ∀ {x y leftError rightError : ℚᵘ} →
  .{{_ : NonNegative rightError}} →
  y ℚ.≤ x ℚ.+ leftError →
  (y ℚ.- x) ℚ.≤ leftError ℚ.+ rightError
differenceUpperFromLeft {x} {y} {leftError} {rightError} y≤x+l =
  let open ℚP.≤-Reasoning in
  begin
    y ℚ.- x
      ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- x) y≤x+l ⟩
    (x ℚ.+ leftError) ℚ.- x
      ≃⟨ ℚP.+-assoc x leftError (ℚ.- x) ⟩
    x ℚ.+ (leftError ℚ.- x)
      ≃⟨ ℚP.+-congʳ x (ℚP.+-comm leftError (ℚ.- x)) ⟩
    x ℚ.+ ((ℚ.- x) ℚ.+ leftError)
      ≃⟨ ℚP.≃-sym (ℚP.+-assoc x (ℚ.- x) leftError) ⟩
    (x ℚ.- x) ℚ.+ leftError
      ≃⟨ ℚP.+-congˡ leftError (ℚP.+-inverseʳ x) ⟩
    ℚ.0ℚᵘ ℚ.+ leftError
      ≃⟨ ℚP.+-identityˡ leftError ⟩
    leftError
      ≤⟨ ℚP.p≤p+q leftError rightError ⟩
    leftError ℚ.+ rightError
  ∎

negDifferenceEquivalentReverse :
  ∀ x y → ℚ.- (x ℚ.- y) ℚ.≃ (y ℚ.- x)
negDifferenceEquivalentReverse x y =
  let open ℚP.≤-Reasoning in
  begin-equality
    ℚ.- (x ℚ.- y)
      ≡⟨ ℚP.neg-distrib-+ x (ℚ.- y) ⟩
    (ℚ.- x) ℚ.+ (ℚ.- (ℚ.- y))
      ≃⟨ ℚP.+-congˡ (ℚ.- (ℚ.- y)) (ℚP.≃-refl {ℚ.- x}) ⟩
    (ℚ.- x) ℚ.+ (ℚ.- (ℚ.- y))
      ≃⟨ ℚP.+-congˡ (ℚ.- (ℚ.- y)) (ℚP.≃-refl {ℚ.- x}) ⟩
    (ℚ.- x) ℚ.+ (ℚ.- (ℚ.- y))
      ≃⟨ ℚP.+-congʳ (ℚ.- x) (ℚP.neg-involutive y) ⟩
    (ℚ.- x) ℚ.+ y
      ≃⟨ ℚP.+-comm (ℚ.- x) y ⟩
    y ℚ.- x
  ∎

absoluteDifferenceBound :
  ∀ {x y leftError rightError : ℚᵘ} →
  .{{_ : NonNegative leftError}} →
  .{{_ : NonNegative rightError}} →
  x ℚ.≤ y ℚ.+ rightError →
  y ℚ.≤ x ℚ.+ leftError →
  ℚ.∣ x ℚ.- y ∣ ℚ.≤ leftError ℚ.+ rightError
absoluteDifferenceBound {x} {y} {leftError} {rightError} x≤y+r y≤x+l
  with ℚP.∣p∣≡p∨∣p∣≡-p (x ℚ.- y)
... | inj₁ absoluteIsPositive =
  subst
    (λ value → value ℚ.≤ leftError ℚ.+ rightError)
    (sym absoluteIsPositive)
    (differenceUpperFromRight x≤y+r)
... | inj₂ absoluteIsNegative =
  ℚP.≤-respˡ-≃
    (ℚP.≃-sym (negDifferenceEquivalentReverse x y))
    (subst
      (λ value → value ℚ.≤ leftError ℚ.+ rightError)
      (sym absoluteIsNegative)
      (differenceUpperFromLeft y≤x+l))
  where
  open import Relation.Binary.PropositionalEquality using (subst; sym)

rationalDirectedDifferenceAbsoluteBoundLevel : ProofLevel
rationalDirectedDifferenceAbsoluteBoundLevel = machineChecked
