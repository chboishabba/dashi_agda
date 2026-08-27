module DASHI.Core.RulePremiseTypingGeometryExact where

------------------------------------------------------------------------
-- RULE PREMISE TYPING GEOMETRY
--
-- Generic owner for a pattern that appears whenever a large rule is recovered
-- in stages.  A source may determine the *kind* of judgement required at each
-- premise position before the exact formula body at that position has been
-- transcribed.
--
-- Keeping the requirement specification separate from its realization avoids
-- promoting a source-level classification into a completed rule body.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record RulePremiseTypeSpecification (Kind : Set) : Set₁ where
  constructor rulePremiseTypeSpecification
  field
    Slot : Set
    requiredKind : Slot → Kind

open RulePremiseTypeSpecification public

record RealizesPremiseTypeSpecification
    {Kind Judgment : Set}
    (classify : Judgment → Kind)
    (specification : RulePremiseTypeSpecification Kind) : Set₁ where
  constructor realizesPremiseTypeSpecification
  field
    premise : Slot specification → Judgment
    premiseHasRequiredKind :
      (slot : Slot specification) →
      classify (premise slot) ≡ requiredKind specification slot

open RealizesPremiseTypeSpecification public

------------------------------------------------------------------------
-- A partial recovery can certify selected slots without requiring the whole
-- rule to be present.  This is useful for source transcription workflows.
------------------------------------------------------------------------

record PartialPremiseTypingReceipt
    {Kind Slot : Set}
    (requiredKind : Slot → Kind) : Set₁ where
  constructor partialPremiseTypingReceipt
  field
    RecoveredSlot : Set
    include : RecoveredSlot → Slot
    recoveredKind : RecoveredSlot → Kind
    agrees :
      (slot : RecoveredSlot) →
      recoveredKind slot ≡ requiredKind (include slot)

open PartialPremiseTypingReceipt public

record RulePremiseTypingGeometryBoundary : Set where
  constructor rulePremiseTypingGeometryBoundary
  field
    premiseKindsCanBeRecoveredBeforeBodies : Bool
    premiseKindsCanBeRecoveredBeforeBodiesIsTrue :
      premiseKindsCanBeRecoveredBeforeBodies ≡ true

    typedRequirementIsAlreadyExactPremiseBody : Bool
    typedRequirementIsAlreadyExactPremiseBodyIsFalse :
      typedRequirementIsAlreadyExactPremiseBody ≡ false

    partialTypingReceiptIsAlreadyCompleteRule : Bool
    partialTypingReceiptIsAlreadyCompleteRuleIsFalse :
      partialTypingReceiptIsAlreadyCompleteRule ≡ false

canonicalRulePremiseTypingGeometryBoundary :
  RulePremiseTypingGeometryBoundary
canonicalRulePremiseTypingGeometryBoundary =
  rulePremiseTypingGeometryBoundary
    true refl
    false refl
    false refl
