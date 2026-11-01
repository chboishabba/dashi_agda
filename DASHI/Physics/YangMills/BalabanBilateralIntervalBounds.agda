module DASHI.Physics.YangMills.BalabanBilateralIntervalBounds where

-- Bilateral bound composition for the arbitrary-interval determinant identity.
--
-- This module does not assume shellwise positivity.  It combines lower and
-- upper bounds on the endpoint determinant difference, the cumulative penalty
-- correction, and the cumulative interaction remainder to obtain the exact
-- interval estimate needed by Bałaban's bilateral logarithmic trajectory.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _≤ℝ_
  ; +-mono-≤
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum
  ; betaIntervalEquality
  ; betaIntervalUpperBound
  )

replaceRight :
  ∀ {a b c : ℝ} →
  a ≤ℝ b →
  b ≡ c →
  a ≤ℝ c
replaceRight a≤b refl = a≤b

combineIntervalLowerBounds :
  ∀ {endpointLower correctionLower interactionLower
      endpointTerm correctionTerm interactionTerm} →
  endpointLower ≤ℝ endpointTerm →
  correctionLower ≤ℝ correctionTerm →
  interactionLower ≤ℝ interactionTerm →
  (endpointLower +ℝ correctionLower) +ℝ interactionLower
    ≤ℝ
  (endpointTerm +ℝ correctionTerm) +ℝ interactionTerm
combineIntervalLowerBounds endpointBound correctionBound interactionBound =
  +-mono-≤
    (+-mono-≤ endpointBound correctionBound)
    interactionBound

betaIntervalLowerBound :
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
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointBound :
    ∀ k n →
    endpointLower k n
      ≤ℝ endpoint (n + k) -ℝ endpoint k) →
  (correctionBound :
    ∀ k n →
    correctionLower k n
      ≤ℝ intervalSum correction k n) →
  (interactionBound :
    ∀ k n →
    interactionLower k n
      ≤ℝ intervalSum interaction k n) →
  ∀ k n →
  (endpointLower k n +ℝ correctionLower k n)
    +ℝ interactionLower k n
    ≤ℝ intervalSum beta k n
betaIntervalLowerBound
  beta gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointLower correctionLower interactionLower
  endpointBound correctionBound interactionBound
  k n =
  let
    bound = combineIntervalLowerBounds
      (endpointBound k n)
      (correctionBound k n)
      (interactionBound k n)
    equality = betaIntervalEquality
      beta gaussian correction interaction endpoint
      totalBeta shellDecomposition k n
  in
    replaceRight bound (sym equality)
  where
    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y →
      y ≡ x
    sym refl = refl

betaIntervalBilateralBound :
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
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n
      ≤ℝ endpoint (n + k) -ℝ endpoint k) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n
      ≤ℝ intervalSum correction k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpper k n) →
  ∀ k n →
  ((endpointLower k n +ℝ correctionLower k n)
      +ℝ interactionLower k n
      ≤ℝ intervalSum beta k n)
  ×
  (intervalSum beta k n
      ≤ℝ
    (endpointUpper k n +ℝ correctionUpper k n)
      +ℝ interactionUpper k n)
betaIntervalBilateralBound
  beta gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  betaIntervalLowerBound
    beta gaussian correction interaction endpoint
    totalBeta shellDecomposition
    endpointLower correctionLower interactionLower
    endpointLowerBound correctionLowerBound interactionLowerBound
    k n
  ,
  betaIntervalUpperBound
    beta gaussian correction interaction endpoint
    totalBeta shellDecomposition
    endpointUpper correctionUpper interactionUpper
    endpointUpperBound correctionUpperBound interactionUpperBound
    k n
