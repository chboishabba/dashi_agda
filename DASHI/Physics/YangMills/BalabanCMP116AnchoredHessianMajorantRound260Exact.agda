{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116AnchoredHessianMajorantRound260Exact where

------------------------------------------------------------------------
-- ROUND260 / SOURCE MARKED COMPARISON + REFERENCE ANCHOR -> ABSOLUTE HESSIAN
--
-- CMP99/109/116 marked resummation controls a comparison/difference between
-- two domain/background realizations.  That theorem must not be silently
-- promoted to an absolute bound on one realization.
--
-- The least-privilege absolute majorant is therefore
--
--   selected = comparison + reference
--   |comparison| <= embed comparisonDebt
--   |reference|  <= embed referenceDebt
--
-- which gives
--
--   |selected| <= embed (comparisonDebt + referenceDebt).
--
-- If a later source theorem identifies a canonical reference with zero, this
-- compiler specializes with `referenceDebt = 0`; no such vanishing theorem is
-- assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _+ℝ_; _≤ℝ_; absAddSubadditive; +-mono-≤; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed

record AnchoredRealHessianMajorant
    (embedding : Embed.OrderedRationalRealRingEmbedding) : Set₁ where
  field
    selected comparison reference : ℝ

    comparisonDebt referenceDebt : ℚ
    comparisonDebtNonnegative : 0ℚ ≤ comparisonDebt
    referenceDebtNonnegative : 0ℚ ≤ referenceDebt

    selectedIsComparisonPlusReference :
      selected ≡ comparison +ℝ reference

    comparisonAbsMajorized :
      absℝ comparison ≤ℝ Embed.embed embedding comparisonDebt

    referenceAbsMajorized :
      absℝ reference ≤ℝ Embed.embed embedding referenceDebt

open AnchoredRealHessianMajorant public

absoluteDebt :
  ∀ {embedding} → AnchoredRealHessianMajorant embedding → ℚ
absoluteDebt dataSet = comparisonDebt dataSet + referenceDebt dataSet

absoluteDebtNonnegative :
  ∀ {embedding}
    (dataSet : AnchoredRealHessianMajorant embedding) →
  0ℚ ≤ absoluteDebt dataSet
absoluteDebtNonnegative dataSet =
  ℚP.+-mono-≤
    (comparisonDebtNonnegative dataSet)
    (referenceDebtNonnegative dataSet)

selectedAbsMajorized :
  ∀ {embedding}
    (dataSet : AnchoredRealHessianMajorant embedding) →
  absℝ (selected dataSet)
  ≤ℝ Embed.embed embedding (absoluteDebt dataSet)
selectedAbsMajorized {embedding} dataSet =
  subst
    (λ right → absℝ (selected dataSet) ≤ℝ right)
    (sym
      (Embed.addExact embedding
        (comparisonDebt dataSet)
        (referenceDebt dataSet)))
    (subst
      (λ left → left
        ≤ℝ Embed.embed embedding (comparisonDebt dataSet)
          +ℝ Embed.embed embedding (referenceDebt dataSet))
      (sym (congAbs (selectedIsComparisonPlusReference dataSet)))
      (≤ℝ-trans
        (absAddSubadditive (comparison dataSet) (reference dataSet))
        (+-mono-≤
          (comparisonAbsMajorized dataSet)
          (referenceAbsMajorized dataSet))))
  where
  congAbs : ∀ {a b : ℝ} → a ≡ b → absℝ a ≡ absℝ b
  congAbs refl = refl

anchoredHessianMajorantCompilerLevel : ProofLevel
anchoredHessianMajorantCompilerLevel = machineChecked

markedComparisonSourceRealizationLevel : ProofLevel
markedComparisonSourceRealizationLevel = conditional

referenceAnchorMajorizationLevel : ProofLevel
referenceAnchorMajorizationLevel = conditional
