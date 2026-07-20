module DASHI.Philosophy.ActionDominationCost where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Ethical assessment tracks which distinctions and continuations are lost,
-- under whose authority, with what reversibility and receipt.  Generic
-- contraction alone is not domination.

data LossAxis : Set where
  voiceLoss :
    LossAxis

  relationLoss :
    LossAxis

  optionLoss :
    LossAxis

  historyLoss :
    LossAxis

  repairLoss :
    LossAxis

canonicalLossAxes :
  List LossAxis
canonicalLossAxes =
  voiceLoss
  ∷ relationLoss
  ∷ optionLoss
  ∷ historyLoss
  ∷ repairLoss
  ∷ []

record TransformationAssessment
       (Transformation State Cost Authority Receipt : Set) : Set₁ where
  field
    transformation :
      Transformation

    before :
      State

    after :
      State

    dominationCost :
      Cost

    authority :
      Authority

    lossReceipt :
      Receipt

    reversible :
      Set

    consentWhereApplicable :
      Set

    viableContinuationsReduced :
      Set

    lossConcealed :
      Set

open TransformationAssessment public

record DominationBoundary : Set where
  constructor mkDominationBoundary
  field
    everyContractionIsDomination :
      Bool

    concealedLossMatters :
      Bool

    authorityAndReversibilityMatter :
      Bool

    receiptRequired :
      Bool

open DominationBoundary public

canonicalDominationBoundary :
  DominationBoundary
canonicalDominationBoundary =
  mkDominationBoundary
    false
    true
    true
    true

canonicalContractionAloneNotDomination :
  everyContractionIsDomination canonicalDominationBoundary
  ≡
  false
canonicalContractionAloneNotDomination =
  refl
