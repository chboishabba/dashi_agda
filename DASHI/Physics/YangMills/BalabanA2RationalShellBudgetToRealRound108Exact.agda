{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2DirectHistoryShellSumRound108Exact as Q

------------------------------------------------------------------------
-- Standard ℚ -> ℝ ordered-ring transport required by the literal CMP109
-- consumer.  This is foundational analysis, not a Yang--Mills estimate.
------------------------------------------------------------------------

record OrderedRationalRealRingEmbedding : Set₁ where
  field
    embed : ℚ → ℝ
    zeroExact : embed 0ℚ ≡ 0ℝ
    oneExact : embed 1ℚ ≡ 1ℝ
    addExact : ∀ a b → embed (a + b) ≡ embed a +ℝ embed b
    strictOrderPreserving : ∀ {a b} → a < b → embed a <ℝ embed b

open OrderedRationalRealRingEmbedding public

sumReal : (Nat → ℝ) → Nat → ℝ
sumReal f zero = 0ℝ
sumReal f (suc n) = sumReal f n +ℝ f n

embedFiniteSum :
  (embedding : OrderedRationalRealRingEmbedding)
  (f : Nat → ℚ) → ∀ K →
  embed embedding (Q.sum f K)
  ≡ sumReal (λ j → embed embedding (f j)) K
embedFiniteSum embedding f zero = zeroExact embedding
embedFiniteSum embedding f (suc n) =
  trans
    (addExact embedding (Q.sum f n) (f n))
    (cong (_+ℝ embed embedding (f n)) (embedFiniteSum embedding f n))

record RealizedDirectHistoryShellBudget (cutoff : Nat) : Set₁ where
  field
    embedding : OrderedRationalRealRingEmbedding
    rationalBudget : Q.DirectHistoryShellBudget cutoff

open RealizedDirectHistoryShellBudget public

realShell :
  ∀ {cutoff} → RealizedDirectHistoryShellBudget cutoff → Nat → ℝ
realShell dataSet j =
  embed (embedding dataSet) (Q.Budget.totalShell (rationalBudget dataSet) j)

realPartialSumBelowOne :
  ∀ {cutoff}
    (dataSet : RealizedDirectHistoryShellBudget cutoff)
    K → K ℕ.≤ cutoff →
  sumReal (realShell dataSet) K <ℝ 1ℝ
realPartialSumBelowOne dataSet K K≤ =
  let
    e = embedding dataSet
    rationalStrict = Q.Budget.totalPartialSumBelowOne
      (rationalBudget dataSet) K K≤
    transported :
      embed e (Q.sum (Q.Budget.totalShell (rationalBudget dataSet)) K)
      <ℝ embed e 1ℚ
    transported = strictOrderPreserving e rationalStrict
  in
  substRight transported
  where
    substRight :
      embed (embedding dataSet)
        (Q.sum (Q.Budget.totalShell (rationalBudget dataSet)) K)
        <ℝ embed (embedding dataSet) 1ℚ →
      sumReal (realShell dataSet) K <ℝ 1ℝ
    substRight proof
      rewrite embedFiniteSum (embedding dataSet)
        (Q.Budget.totalShell (rationalBudget dataSet)) K
            | oneExact (embedding dataSet) = proof

round108A2RationalToRealShellSumLevel : ProofLevel
round108A2RationalToRealShellSumLevel = machineChecked

orderedRationalRealRingEmbeddingLevel : ProofLevel
orderedRationalRealRingEmbeddingLevel = standardImported

-- Physical A2 leaf now has the exact form required by Round103:
-- prove, on two literal generated histories,
--
--   |beta_j(u)-beta_j(v)| <= realShell_j |u-v|.
--
-- The finite real sum of those coefficients is theoremically < 1.
literalCMP109RealShellLipschitzRound108Level : ProofLevel
literalCMP109RealShellLipschitzRound108Level = conditional
