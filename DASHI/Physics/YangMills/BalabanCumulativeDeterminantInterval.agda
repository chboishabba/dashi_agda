module DASHI.Physics.YangMills.BalabanCumulativeDeterminantInterval where

-- Canonical cumulative determinant bridge.
--
-- The adjacent Gaussian telescope is not assumed.  Instead the block
-- calculation may provide directly, on every interval,
--
--   sum Gaussian = endpointDifference + J_{k:n},
--
-- where J_{k:n} is the exact cumulative penalty/block-factor correction.  This
-- module combines that identity with the shellwise decomposition
-- beta = Gaussian + interaction and proves the total interval equality and its
-- one-sided and bilateral bound consequences.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _≤ℝ_
  ; +-mono-≤
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum
  ; intervalSumPointwiseAdd
  )

sym :
  ∀ {A : Set} {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

cumulativeDeterminantBetaEquality :
  (beta gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  ∀ k n →
  intervalSum beta k n
    ≡ (endpointDifference k n +ℝ cumulativeCorrection k n)
        +ℝ intervalSum interaction k n
cumulativeDeterminantBetaEquality
  beta gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity k n =
  let
    p1 = intervalSumPointwiseAdd
      beta gaussian interaction totalBeta k n
    p2 = cong
      (λ gaussianPrefix →
        gaussianPrefix +ℝ intervalSum interaction k n)
      (cumulativeGaussianIdentity k n)
  in
    trans p1 p2

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

combineLower :
  ∀ {endpointLower correctionLower interactionLower
      endpointTerm correctionTerm interactionTerm} →
  endpointLower ≤ℝ endpointTerm →
  correctionLower ≤ℝ correctionTerm →
  interactionLower ≤ℝ interactionTerm →
  (endpointLower +ℝ correctionLower) +ℝ interactionLower
    ≤ℝ
  (endpointTerm +ℝ correctionTerm) +ℝ interactionTerm
combineLower endpointBound correctionBound interactionBound =
  +-mono-≤
    (+-mono-≤ endpointBound correctionBound)
    interactionBound

combineUpper :
  ∀ {endpointTerm correctionTerm interactionTerm
      endpointUpper correctionUpper interactionUpper} →
  endpointTerm ≤ℝ endpointUpper →
  correctionTerm ≤ℝ correctionUpper →
  interactionTerm ≤ℝ interactionUpper →
  (endpointTerm +ℝ correctionTerm) +ℝ interactionTerm
    ≤ℝ
  (endpointUpper +ℝ correctionUpper) +ℝ interactionUpper
combineUpper endpointBound correctionBound interactionBound =
  +-mono-≤
    (+-mono-≤ endpointBound correctionBound)
    interactionBound

cumulativeDeterminantBetaLowerBound :
  (beta gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n ≤ℝ endpointDifference k n) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n ≤ℝ cumulativeCorrection k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n ≤ℝ intervalSum interaction k n) →
  ∀ k n →
  (endpointLower k n +ℝ correctionLower k n)
    +ℝ interactionLower k n
    ≤ℝ intervalSum beta k n
cumulativeDeterminantBetaLowerBound
  beta gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointLower correctionLower interactionLower
  endpointLowerBound correctionLowerBound interactionLowerBound
  k n =
  replaceRight
    (combineLower
      (endpointLowerBound k n)
      (correctionLowerBound k n)
      (interactionLowerBound k n))
    (sym
      (cumulativeDeterminantBetaEquality
        beta gaussian interaction
        endpointDifference cumulativeCorrection
        totalBeta cumulativeGaussianIdentity k n))

cumulativeDeterminantBetaUpperBound :
  (beta gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointUpperBound :
    ∀ k n →
    endpointDifference k n ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    cumulativeCorrection k n ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n ≤ℝ interactionUpper k n) →
  ∀ k n →
  intervalSum beta k n
    ≤ℝ
  (endpointUpper k n +ℝ correctionUpper k n)
    +ℝ interactionUpper k n
cumulativeDeterminantBetaUpperBound
  beta gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointUpper correctionUpper interactionUpper
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  replaceLeft
    (cumulativeDeterminantBetaEquality
      beta gaussian interaction
      endpointDifference cumulativeCorrection
      totalBeta cumulativeGaussianIdentity k n)
    (combineUpper
      (endpointUpperBound k n)
      (correctionUpperBound k n)
      (interactionUpperBound k n))

cumulativeDeterminantBetaBilateralBound :
  (beta gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n ≤ℝ endpointDifference k n) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n ≤ℝ cumulativeCorrection k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpointDifference k n ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    cumulativeCorrection k n ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n ≤ℝ interactionUpper k n) →
  ∀ k n →
  ((endpointLower k n +ℝ correctionLower k n)
      +ℝ interactionLower k n
      ≤ℝ intervalSum beta k n)
  ×
  (intervalSum beta k n
      ≤ℝ
    (endpointUpper k n +ℝ correctionUpper k n)
      +ℝ interactionUpper k n)
cumulativeDeterminantBetaBilateralBound
  beta gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  cumulativeDeterminantBetaLowerBound
    beta gaussian interaction
    endpointDifference cumulativeCorrection
    totalBeta cumulativeGaussianIdentity
    endpointLower correctionLower interactionLower
    endpointLowerBound correctionLowerBound interactionLowerBound
    k n
  ,
  cumulativeDeterminantBetaUpperBound
    beta gaussian interaction
    endpointDifference cumulativeCorrection
    totalBeta cumulativeGaussianIdentity
    endpointUpper correctionUpper interactionUpper
    endpointUpperBound correctionUpperBound interactionUpperBound
    k n
