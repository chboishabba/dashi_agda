module DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra where

-- Additive algebra for the cumulative determinant route on an arbitrary scale
-- interval.  This module owns the finite summation and telescoping steps:
--
--   βⱼ = Gaussianⱼ + Interactionⱼ
--   Gaussianⱼ = (Dⱼ - Dⱼ₋₁) + Jⱼ
--
-- imply
--
--   Σ_{j=k+1}^{k+n} βⱼ
--     = (D_{k+n} - D_k)
--       + Σ Jⱼ
--       + Σ Interactionⱼ.
--
-- The source-specific shell identity and analytic estimates remain arguments;
-- the cumulative equality and bound composition are proved here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _≤ℝ_
  ; +-identityˡ
  ; +-comm
  ; +-assoc
  ; +-mono-≤
  ; subSelf
  ; subAddCancelMiddle
  ; cong
  ; trans
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Shells in an interval of length `n` beginning after scale `k` are indexed
-- k+1,...,k+n.
intervalSum : (ℕ → ℝ) → ℕ → ℕ → ℝ
intervalSum f k zero = 0ℝ
intervalSum f k (suc n) =
  intervalSum f k n +ℝ f (suc (n + k))

rearrangeAdd4 :
  ∀ a b c d →
  (a +ℝ b) +ℝ (c +ℝ d)
    ≡ (a +ℝ c) +ℝ (b +ℝ d)
rearrangeAdd4 a b c d =
  let
    p1 = +-assoc a b (c +ℝ d)
    p2 = sym (+-assoc b c d)
    p3 = +-comm b c
    p4 = +-assoc c b d
    p5 = trans p2 (trans (cong (λ x → x +ℝ d) p3) p4)
    p6 = cong (λ x → a +ℝ x) p5
    p7 = sym (+-assoc a c (b +ℝ d))
  in
    trans p1 (trans p6 p7)

-- Finite interval summation respects a pointwise shell decomposition.
intervalSumPointwiseAdd :
  (total left right : ℕ → ℝ) →
  (∀ j → total (suc j) ≡ left (suc j) +ℝ right (suc j)) →
  ∀ k n →
  intervalSum total k n
    ≡ intervalSum left k n +ℝ intervalSum right k n
intervalSumPointwiseAdd total left right pointwise k zero =
  sym (+-identityˡ 0ℝ)
intervalSumPointwiseAdd total left right pointwise k (suc n) =
  let
    index = n + k
    shell = pointwise index
    ih = intervalSumPointwiseAdd total left right pointwise k n
    p1 = cong (λ x → intervalSum total k n +ℝ x) shell
    p2 = cong
      (λ x → x +ℝ (left (suc index) +ℝ right (suc index)))
      ih
    p3 = rearrangeAdd4
      (intervalSum left k n)
      (intervalSum right k n)
      (left (suc index))
      (right (suc index))
  in
    trans p1 (trans p2 p3)

endpointShell : (ℕ → ℝ) → ℕ → ℝ
endpointShell endpoint zero = 0ℝ
endpointShell endpoint (suc j) =
  endpoint (suc j) -ℝ endpoint j

-- The endpoint increments telescope on every interval, not only from zero.
endpointIntervalTelescopes :
  (endpoint : ℕ → ℝ) →
  ∀ k n →
  intervalSum (endpointShell endpoint) k n
    ≡ endpoint (n + k) -ℝ endpoint k
endpointIntervalTelescopes endpoint k zero =
  sym (subSelf (endpoint k))
endpointIntervalTelescopes endpoint k (suc n) =
  let
    middle = endpoint (n + k)
    final = endpoint (suc (n + k))
    start = endpoint k
    current = final -ℝ middle
    ih = endpointIntervalTelescopes endpoint k n
    p1 = cong (λ x → x +ℝ current) ih
    p2 = +-comm (middle -ℝ start) current
    p3 = subAddCancelMiddle final middle start
  in
    trans p1 (trans p2 p3)

-- A Gaussian shell identity produces endpoint telescoping plus the explicit
-- cumulative penalty/Jacobian correction.
gaussianIntervalTelescopes :
  (gaussian correction endpoint : ℕ → ℝ) →
  (shellDecomposition :
    ∀ j →
    gaussian (suc j)
      ≡ (endpoint (suc j) -ℝ endpoint j)
          +ℝ correction (suc j)) →
  ∀ k n →
  intervalSum gaussian k n
    ≡ (endpoint (n + k) -ℝ endpoint k)
        +ℝ intervalSum correction k n
gaussianIntervalTelescopes gaussian correction endpoint shellDecomposition k n =
  let
    p1 = intervalSumPointwiseAdd
      gaussian
      (endpointShell endpoint)
      correction
      shellDecomposition
      k n
    p2 = cong
      (λ x → x +ℝ intervalSum correction k n)
      (endpointIntervalTelescopes endpoint k n)
  in
    trans p1 p2

-- Full arbitrary-interval beta identity.
betaIntervalEquality :
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
  ∀ k n →
  intervalSum beta k n
    ≡ ((endpoint (n + k) -ℝ endpoint k)
        +ℝ intervalSum correction k n)
        +ℝ intervalSum interaction k n
betaIntervalEquality
  beta gaussian correction interaction endpoint
  totalBeta shellDecomposition k n =
  let
    p1 = intervalSumPointwiseAdd
      beta gaussian interaction totalBeta k n
    p2 = gaussianIntervalTelescopes
      gaussian correction endpoint shellDecomposition k n
    p3 = cong
      (λ x → x +ℝ intervalSum interaction k n)
      p2
  in
    trans p1 p3

combineIntervalUpperBounds :
  ∀ {endpointTerm correctionTerm interactionTerm
      endpointUpper correctionUpper interactionUpper} →
  endpointTerm ≤ℝ endpointUpper →
  correctionTerm ≤ℝ correctionUpper →
  interactionTerm ≤ℝ interactionUpper →
  (endpointTerm +ℝ correctionTerm) +ℝ interactionTerm
    ≤ℝ
  (endpointUpper +ℝ correctionUpper) +ℝ interactionUpper
combineIntervalUpperBounds endpointBound correctionBound interactionBound =
  +-mono-≤
    (+-mono-≤ endpointBound correctionBound)
    interactionBound

-- The cumulative equality transports componentwise analytic bounds to the
-- desired interval beta upper bound.
betaIntervalUpperBound :
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
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpper k n) →
  (correctionBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpper k n) →
  (interactionBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpper k n) →
  ∀ k n →
  intervalSum beta k n
    ≤ℝ
  (endpointUpper k n +ℝ correctionUpper k n)
    +ℝ interactionUpper k n
betaIntervalUpperBound
  beta gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointUpper correctionUpper interactionUpper
  endpointBound correctionBound interactionBound
  k n =
  let
    equality = betaIntervalEquality
      beta gaussian correction interaction endpoint
      totalBeta shellDecomposition k n
    bound = combineIntervalUpperBounds
      (endpointBound k n)
      (correctionBound k n)
      (interactionBound k n)
  in
    replaceLeft equality bound
  where
    replaceLeft :
      ∀ {a b c : ℝ} →
      a ≡ b →
      b ≤ℝ c →
      a ≤ℝ c
    replaceLeft refl b≤c = b≤c
