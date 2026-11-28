module DASHI.Physics.YangMills.YMClayContinuousWilsonArithmeticStrictnessExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; _≤ℝ_; _<ℝ_; zeroLtOne; oneNonnegative;
   ≤ℝ-refl; notLeOfLt; subSelf; mulZeroˡ)

import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.YMClayOriginalWilsonContinuousA2BridgeExact as A2

unrestrictedMeanRestrictionBoundsImpossible :
  ∀ {Converges : (Nat → ℝ) → ℝ → Set}
    (quotient : Quotient.RealQuotientConvergenceAuthority Converges)
    (arithmetic : A2.ContinuousWilsonArithmetic quotient) →
    (∀ {Configuration : Set}
       (E : (Configuration → ℝ) → ℝ)
       (addLaw : ∀ f g → E (λ x → f x +ℝ g x) ≡ E f +ℝ E g)
       (scaleLaw : ∀ scalar f → E (λ x → scalar *ℝ f x) ≡ scalar *ℝ E f)
       (positiveLaw : ∀ f → (∀ x → 0ℝ ≤ℝ f x) → 0ℝ ≤ℝ E f)
       (extLaw : ∀ f g → (∀ x → f x ≡ g x) → E f ≡ E g)
       (χ h : Configuration → ℝ) (q goodMean m M : ℝ) →
       (∀ x → 0ℝ ≤ℝ χ x) →
       (∀ x → χ x ≤ℝ 1ℝ) →
       (∀ x → m ≤ℝ h x) →
       (∀ x → h x ≤ℝ M) →
       goodMean ≡ E (λ x → (1ℝ -ℝ χ x) *ℝ h x) →
       q ≡ E χ →
       (m *ℝ q ≤ℝ E (λ x → χ x *ℝ h x)) ×
       (E (λ x → χ x *ℝ h x) ≤ℝ M *ℝ q) ×
       (m ≤ℝ Quotient.divide quotient goodMean (1ℝ -ℝ q)) ×
       (Quotient.divide quotient goodMean (1ℝ -ℝ q) ≤ℝ M)) →
    ⊥
unrestrictedMeanRestrictionBoundsImpossible quotient arithmetic old =
  let
    D : ℝ
    D = Quotient.divide quotient 0ℝ (1ℝ -ℝ 1ℝ)

    M : ℝ
    M = D +ℝ 1ℝ

    E : (⊤ → ℝ) → ℝ
    E f = f tt

    χ : ⊤ → ℝ
    χ _ = 1ℝ

    h : ⊤ → ℝ
    h _ = M

    addLaw : ∀ f g → E (λ x → f x +ℝ g x) ≡ E f +ℝ E g
    addLaw f g = refl

    scaleLaw : ∀ scalar f → E (λ x → scalar *ℝ f x) ≡ scalar *ℝ E f
    scaleLaw scalar f = refl

    positiveLaw : ∀ f → (∀ x → 0ℝ ≤ℝ f x) → 0ℝ ≤ℝ E f
    positiveLaw f nonnegative = nonnegative tt

    extLaw : ∀ f g → (∀ x → f x ≡ g x) → E f ≡ E g
    extLaw f g equal = equal tt

    goodMeanEq : 0ℝ ≡ E (λ x → (1ℝ -ℝ χ x) *ℝ h x)
    goodMeanEq =
      trans
        (sym (mulZeroˡ M))
        (cong (λ value → value *ℝ M) (sym (subSelf 1ℝ)))

    qEq : 1ℝ ≡ E χ
    qEq = refl

    bounds =
      old E addLaw scaleLaw positiveLaw extLaw χ h 1ℝ 0ℝ M M
        (λ _ → oneNonnegative)
        (λ _ → ≤ℝ-refl)
        (λ _ → ≤ℝ-refl)
        (λ _ → ≤ℝ-refl)
        goodMeanEq qEq

    lowerLe : M ≤ℝ D
    lowerLe = proj₁ (proj₂ (proj₂ bounds))

    dLtM : D <ℝ M
    dLtM = A2.ContinuousWilsonArithmetic.positiveAddRight arithmetic zeroLtOne
  in
  notLeOfLt dLtM lowerLe
