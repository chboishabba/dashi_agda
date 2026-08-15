module DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the order/arithmetic induction used after Luo's fixed-b recursion.
-- Given
--
--   A_(n+1) <= q A_n + R_n,
--   R_n     <= (r-q) C r^n,
--   A_0     <= C,
--   0 <= q <= r,
--
-- prove A_n <= C r^n for every block index n.  The PDE-specific task is now
-- only to identify A_n with max(E_p,D_p), and to prove the correction budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

power : ℚ → Nat → ℚ
power ratio zero = 1ℚ
power ratio (suc n) = ratio * power ratio n

scaledTarget : ℚ → ℚ → Nat → ℚ
scaledTarget constant ratio n = constant * power ratio n

record RationalFixedBlockDecay : Set where
  field
    sequence correction : Nat → ℚ
    q r constant : ℚ

    qNonnegative : 0ℚ ≤ q
    rNonnegative : 0ℚ ≤ r
    constantNonnegative : 0ℚ ≤ constant
    qBelowR : q ≤ r

    initialBound : sequence zero ≤ constant

    recursion :
      (n : Nat) →
      sequence (suc n) ≤ q * sequence n + correction n

    correctionBudget :
      (n : Nat) →
      correction n ≤ (r - q) * scaledTarget constant r n

open RationalFixedBlockDecay public

powerNonnegative :
  (ratio : ℚ) → 0ℚ ≤ ratio →
  (n : Nat) → 0ℚ ≤ power ratio n
powerNonnegative ratio ratioNN zero = ℚₚ.nonNegative⁻¹ 1ℚ
powerNonnegative ratio ratioNN (suc n) =
  let
    instance
      ratioNonnegative = nonNegative ratioNN
      tailNonnegative = nonNegative (powerNonnegative ratio ratioNN n)
      productNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg ratio (power ratio n)
  in
  ℚₚ.nonNegative⁻¹ (ratio * power ratio n)

scaledTargetNonnegative :
  (constant ratio : ℚ) →
  0ℚ ≤ constant → 0ℚ ≤ ratio →
  (n : Nat) → 0ℚ ≤ scaledTarget constant ratio n
scaledTargetNonnegative constant ratio constantNN ratioNN n =
  let
    instance
      constantNonnegative = nonNegative constantNN
      powerNonnegativeInstance =
        nonNegative (powerNonnegative ratio ratioNN n)
      scaledTargetNonnegativeInstance =
        ℚₚ.nonNeg*nonNeg⇒nonNeg constant (power ratio n)
  in
  ℚₚ.nonNegative⁻¹ (scaledTarget constant ratio n)

qTimesInductiveBound :
  (certificate : RationalFixedBlockDecay) →
  (n : Nat) →
  sequence certificate n
    ≤ scaledTarget (constant certificate) (r certificate) n →
  q certificate * sequence certificate n
    ≤ q certificate
      * scaledTarget (constant certificate) (r certificate) n
qTimesInductiveBound certificate n inductionHypothesis =
  let instance qNN = nonNegative (qNonnegative certificate)
  in ℚₚ.*-monoˡ-≤-nonNeg
    (q certificate) inductionHypothesis

combineStepBudgets :
  (certificate : RationalFixedBlockDecay) →
  (n : Nat) →
  q certificate
      * scaledTarget (constant certificate) (r certificate) n
    +
  (r certificate - q certificate)
      * scaledTarget (constant certificate) (r certificate) n
  ≡ scaledTarget (constant certificate) (r certificate) (suc n)
private
  combineStepBudgetsAlgebra :
    (q r c p : ℚ) →
    q * (c * p) + (r - q) * (c * p) ≡ c * (r * p)
  combineStepBudgetsAlgebra q r c p = solve (q ∷ r ∷ c ∷ p ∷ [])

combineStepBudgets certificate n =
  combineStepBudgetsAlgebra
    (q certificate) (r certificate) (constant certificate)
    (power (r certificate) n)

fixedBlockDecay :
  (certificate : RationalFixedBlockDecay) →
  (n : Nat) →
  sequence certificate n
    ≤ scaledTarget (constant certificate) (r certificate) n
fixedBlockDecay certificate zero
  rewrite ℚₚ.*-identityʳ (constant certificate) =
  initialBound certificate
fixedBlockDecay certificate (suc n) =
  let
    inductionHypothesis = fixedBlockDecay certificate n
    qStage = qTimesInductiveBound certificate n inductionHypothesis
    correctionStage = correctionBudget certificate n
    combined = ℚₚ.+-mono-≤ qStage correctionStage
    recursive = ℚₚ.≤-trans (recursion certificate n) combined
  in
  subst
    (λ upper → sequence certificate (suc n) ≤ upper)
    (combineStepBudgets certificate n)
    recursive

rationalFixedBlockDecayInductionClosed : Bool
rationalFixedBlockDecayInductionClosed = true

rationalFixedBlockDecayInductionClosedIsTrue :
  rationalFixedBlockDecayInductionClosed ≡ true
rationalFixedBlockDecayInductionClosedIsTrue = refl
