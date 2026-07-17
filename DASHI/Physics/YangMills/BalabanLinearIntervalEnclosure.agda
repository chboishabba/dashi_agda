module DASHI.Physics.YangMills.BalabanLinearIntervalEnclosure where

-- Linear-slope specialisation of the bilateral interval theorem.
--
-- Component estimates of the form
--
--   slope * intervalLength
--
-- combine into the bilateral linear beta enclosure used in Bałaban's
-- logarithmic coupling bounds.  The source still has to prove the six
-- component slope estimates; this module owns their exact arithmetic
-- composition.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
  ; _≤ℝ_
  ; *-distribʳ-+
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanBilateralIntervalBounds using
  ( betaIntervalBilateralBound )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

fromNatℝ : ℕ → ℝ
fromNatℝ zero = 0ℝ
fromNatℝ (suc n) = fromNatℝ n +ℝ 1ℝ

combineThreeLinearTerms :
  ∀ a b c n →
  ((a *ℝ n) +ℝ (b *ℝ n)) +ℝ (c *ℝ n)
    ≡ ((a +ℝ b) +ℝ c) *ℝ n
combineThreeLinearTerms a b c n =
  trans
    (cong
      (λ first → first +ℝ (c *ℝ n))
      (sym (*-distribʳ-+ a b n)))
    (sym (*-distribʳ-+ (a +ℝ b) c n))

replaceLeft :
  ∀ {a b c : ℝ} →
  a ≡ b →
  b ≤ℝ c →
  a ≤ℝ c
replaceLeft refl b≤c = b≤c

replaceRight :
  ∀ {a b c : ℝ} →
  a ≤ℝ b →
  b ≡ c →
  a ≤ℝ c
replaceRight a≤b refl = a≤b

betaLinearIntervalBilateralBound :
  (beta gaussian correction interaction endpoint : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (shellDecomposition :
    ∀ j →
    gaussian (suc j)
      ≡ (endpoint (suc j) -ℝ endpoint j)
          +ℝ correction (suc j)) →
  (endpointLowerSlope correctionLowerSlope interactionLowerSlope : ℝ) →
  (endpointUpperSlope correctionUpperSlope interactionUpperSlope : ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLowerSlope *ℝ fromNatℝ n
      ≤ℝ endpoint (n + k) -ℝ endpoint k) →
  (correctionLowerBound :
    ∀ k n →
    correctionLowerSlope *ℝ fromNatℝ n
      ≤ℝ intervalSum correction k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLowerSlope *ℝ fromNatℝ n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpperSlope *ℝ fromNatℝ n) →
  (correctionUpperBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpperSlope *ℝ fromNatℝ n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpperSlope *ℝ fromNatℝ n) →
  ∀ k n →
  (((endpointLowerSlope +ℝ correctionLowerSlope)
      +ℝ interactionLowerSlope) *ℝ fromNatℝ n
      ≤ℝ intervalSum beta k n)
  ×
  (intervalSum beta k n
      ≤ℝ
    ((endpointUpperSlope +ℝ correctionUpperSlope)
      +ℝ interactionUpperSlope) *ℝ fromNatℝ n)
betaLinearIntervalBilateralBound
  beta gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointLowerSlope correctionLowerSlope interactionLowerSlope
  endpointUpperSlope correctionUpperSlope interactionUpperSlope
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  let
    raw = betaIntervalBilateralBound
      beta gaussian correction interaction endpoint
      totalBeta shellDecomposition
      (λ i length → endpointLowerSlope *ℝ fromNatℝ length)
      (λ i length → correctionLowerSlope *ℝ fromNatℝ length)
      (λ i length → interactionLowerSlope *ℝ fromNatℝ length)
      (λ i length → endpointUpperSlope *ℝ fromNatℝ length)
      (λ i length → correctionUpperSlope *ℝ fromNatℝ length)
      (λ i length → interactionUpperSlope *ℝ fromNatℝ length)
      endpointLowerBound correctionLowerBound interactionLowerBound
      endpointUpperBound correctionUpperBound interactionUpperBound
      k n

    lowerEquality = combineThreeLinearTerms
      endpointLowerSlope correctionLowerSlope interactionLowerSlope
      (fromNatℝ n)
    upperEquality = combineThreeLinearTerms
      endpointUpperSlope correctionUpperSlope interactionUpperSlope
      (fromNatℝ n)
  in
    replaceLeft (sym lowerEquality) (proj₁ raw)
  ,
    replaceRight (proj₂ raw) upperEquality
