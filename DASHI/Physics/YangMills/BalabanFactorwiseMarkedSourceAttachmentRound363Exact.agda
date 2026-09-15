{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFactorwiseMarkedSourceAttachmentRound363Exact where

------------------------------------------------------------------------
-- ROUND363 / H_factor = SOURCE FACTOR BOUNDS + LITERAL FACTOR ATTACHMENT
--
-- The existing differentiated-factor telescope proves the complete product
-- replacement bound once each literal factor satisfies:
--
--   |f_i| <= b_i,
--   |g_i| <= b_i,
--   |f_i - g_i| <= m_i.
--
-- CMP109 supplies the ordinary differentiated tree-factor bounds and CMP99(3)
-- supplies the marked changed-factor/domain-discrepancy bound.  The remaining
-- application seam is to identify the selected literal factors/majorants with
-- those source objects on the SAME factor index.
--
-- This module proves only that source-to-selected transport.  The finite
-- telescope remains owned by BalabanDifferentiatedMarkedFactorProductExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record FactorwiseMarkedSource (Factor : Set) : Set₁ where
  field
    leftSource rightSource : Factor → ℝ
    ordinarySource markedSource : Factor → ℝ

    ordinaryLeftBound : ∀ factor →
      absℝ (leftSource factor) ≤ℝ ordinarySource factor

    ordinaryRightBound : ∀ factor →
      absℝ (rightSource factor) ≤ℝ ordinarySource factor

    markedDifferenceBound : ∀ factor →
      absℝ (leftSource factor -ℝ rightSource factor)
        ≤ℝ markedSource factor

open FactorwiseMarkedSource public

record LiteralFactorwiseAttachment {Factor : Set}
    (source : FactorwiseMarkedSource Factor) : Set₁ where
  field
    selectedLeft selectedRight : Factor → ℝ
    selectedOrdinary selectedMarked : Factor → ℝ

    selectedLeftIsSource : selectedLeft ≡ leftSource source
    selectedRightIsSource : selectedRight ≡ rightSource source
    selectedOrdinaryIsSource : selectedOrdinary ≡ ordinarySource source
    selectedMarkedIsSource : selectedMarked ≡ markedSource source

open LiteralFactorwiseAttachment public

selectedOrdinaryLeftBound :
  ∀ {Factor}
    (source : FactorwiseMarkedSource Factor)
    (attachment : LiteralFactorwiseAttachment source)
    (factor : Factor) →
  absℝ (selectedLeft attachment factor)
    ≤ℝ selectedOrdinary attachment factor
selectedOrdinaryLeftBound source attachment factor =
  subst
    (λ left → absℝ left ≤ℝ selectedOrdinary attachment factor)
    (sym (congAt (selectedLeftIsSource attachment) factor))
    (subst
      (λ ordinary → absℝ (leftSource source factor) ≤ℝ ordinary)
      (sym (congAt (selectedOrdinaryIsSource attachment) factor))
      (ordinaryLeftBound source factor))
  where
  congAt : ∀ {A B : Set} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
  congAt refl x = refl

selectedOrdinaryRightBound :
  ∀ {Factor}
    (source : FactorwiseMarkedSource Factor)
    (attachment : LiteralFactorwiseAttachment source)
    (factor : Factor) →
  absℝ (selectedRight attachment factor)
    ≤ℝ selectedOrdinary attachment factor
selectedOrdinaryRightBound source attachment factor =
  subst
    (λ right → absℝ right ≤ℝ selectedOrdinary attachment factor)
    (sym (congAt (selectedRightIsSource attachment) factor))
    (subst
      (λ ordinary → absℝ (rightSource source factor) ≤ℝ ordinary)
      (sym (congAt (selectedOrdinaryIsSource attachment) factor))
      (ordinaryRightBound source factor))
  where
  congAt : ∀ {A B : Set} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
  congAt refl x = refl

selectedMarkedDifferenceBound :
  ∀ {Factor}
    (source : FactorwiseMarkedSource Factor)
    (attachment : LiteralFactorwiseAttachment source)
    (factor : Factor) →
  absℝ
    (selectedLeft attachment factor -ℝ selectedRight attachment factor)
    ≤ℝ selectedMarked attachment factor
selectedMarkedDifferenceBound source attachment factor =
  subst
    (λ left →
      absℝ (left -ℝ selectedRight attachment factor)
        ≤ℝ selectedMarked attachment factor)
    (sym (congAt (selectedLeftIsSource attachment) factor))
    (subst
      (λ right →
        absℝ (leftSource source factor -ℝ right)
          ≤ℝ selectedMarked attachment factor)
      (sym (congAt (selectedRightIsSource attachment) factor))
      (subst
        (λ marked →
          absℝ
            (leftSource source factor -ℝ rightSource source factor)
            ≤ℝ marked)
        (sym (congAt (selectedMarkedIsSource attachment) factor))
        (markedDifferenceBound source factor)))
  where
  congAt : ∀ {A B : Set} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
  congAt refl x = refl

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

cmp109OrdinaryDifferentiatedFactorBoundLevel : ProofLevel
cmp109OrdinaryDifferentiatedFactorBoundLevel = standardImported

cmp99MarkedChangedFactorBoundLevel : ProofLevel
cmp99MarkedChangedFactorBoundLevel = standardImported

literalCMP109FactorFamilyAttachmentLevel : ProofLevel
literalCMP109FactorFamilyAttachmentLevel = conditional

literalCMP99MarkedFactorAttachmentLevel : ProofLevel
literalCMP99MarkedFactorAttachmentLevel = conditional

factorwiseSourceTransportCompilerLevel : ProofLevel
factorwiseSourceTransportCompilerLevel = machineChecked

finiteFactorTelescopeAlreadyOwned : Bool
finiteFactorTelescopeAlreadyOwned = true

finiteFactorTelescopeAlreadyOwnedIsTrue :
  finiteFactorTelescopeAlreadyOwned ≡ true
finiteFactorTelescopeAlreadyOwnedIsTrue = refl

freshWholeProductMarkedEstimateRequired : Bool
freshWholeProductMarkedEstimateRequired = false

freshWholeProductMarkedEstimateRequiredIsFalse :
  freshWholeProductMarkedEstimateRequired ≡ false
freshWholeProductMarkedEstimateRequiredIsFalse = refl

record Round363Boundary : Set where
  constructor round363-boundary
  field
    ordinarySourceFactorBoundsOwned : Bool
    ordinarySourceFactorBoundsOwnedIsTrue :
      ordinarySourceFactorBoundsOwned ≡ true

    markedSourceFactorBoundOwned : Bool
    markedSourceFactorBoundOwnedIsTrue :
      markedSourceFactorBoundOwned ≡ true

    literalFactorAttachmentStillOpen : Bool
    literalFactorAttachmentStillOpenIsTrue :
      literalFactorAttachmentStillOpen ≡ true

canonicalRound363Boundary : Round363Boundary
canonicalRound363Boundary =
  round363-boundary true refl true refl true refl

round363FrontierRefinementLevel : ProofLevel
round363FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
