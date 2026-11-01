module DASHI.Physics.YangMills.BalabanBlockDeterminantLogAdditivity where

-- Convert the multiplicative block-Cholesky product into the additive
-- trace-log identity used by the beta projection.
--
-- The determinant carrier and logarithm implementation remain generic.  The
-- only external algebraic facts required are log(1)=0 and
-- log(a*b)=log(a)+log(b).  Finite product-to-sum conversion and the endpoint
-- identity are proved here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanBlockDeterminantProduct using
  ( intervalProduct
  ; blockDeterminantIntervalFromStep
  )

-- Shift a conditional factor indexed by r into the beta-shell convention,
-- where shell suc r is the step from r to suc r.
conditionalLogShell :
  {Scalar : Set} →
  (Scalar → ℝ) →
  (ℕ → Scalar) →
  ℕ → ℝ
conditionalLogShell logDet conditional zero = 0ℝ
conditionalLogShell logDet conditional (suc r) =
  logDet (conditional r)

intervalProductLog :
  {Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (conditional : ℕ → Scalar) →
  (logDet : Scalar → ℝ) →
  logDet one ≡ 0ℝ →
  (∀ a b → logDet (a * b) ≡ logDet a +ℝ logDet b) →
  ∀ k n →
  logDet (intervalProduct one _*_ conditional k n)
    ≡ intervalSum (conditionalLogShell logDet conditional) k n
intervalProductLog
  one _*_ conditional logDet logOne logMul k zero = logOne
intervalProductLog
  one _*_ conditional logDet logOne logMul k (suc n) =
  let
    index = n + k
    prefix = intervalProduct one _*_ conditional k n
    p1 = logMul prefix (conditional index)
    p2 = cong
      (λ prefixLog → prefixLog +ℝ logDet (conditional index))
      (intervalProductLog
        one _*_ conditional logDet logOne logMul k n)
  in
    trans p1 p2

-- Endpoint log determinant difference as the sum of conditional shell logs.
blockDeterminantLogIntervalFromStep :
  {Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (determinant conditional : ℕ → Scalar) →
  (step :
    ∀ j →
    determinant (suc j) ≡ determinant j * conditional j) →
  (logDet : Scalar → ℝ) →
  logDet one ≡ 0ℝ →
  (logMul : ∀ a b → logDet (a * b) ≡ logDet a +ℝ logDet b) →
  ∀ k n →
  logDet (determinant (n + k))
    ≡ logDet (determinant k)
        +ℝ intervalSum (conditionalLogShell logDet conditional) k n
blockDeterminantLogIntervalFromStep
  one _*_ assoc rightIdentity
  determinant conditional step
  logDet logOne logMul k n =
  let
    product = intervalProduct one _*_ conditional k n
    factorisation = blockDeterminantIntervalFromStep
      one _*_ determinant conditional
      assoc rightIdentity step k n
    p1 = cong logDet factorisation
    p2 = logMul (determinant k) product
    p3 = cong
      (λ conditionalSum → logDet (determinant k) +ℝ conditionalSum)
      (intervalProductLog
        one _*_ conditional logDet logOne logMul k n)
  in
    trans p1 (trans p2 p3)
