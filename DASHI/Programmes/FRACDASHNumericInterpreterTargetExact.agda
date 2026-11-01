module DASHI.Programmes.FRACDASHNumericInterpreterTargetExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI target for the remaining FRACDASH numeric-interpreter gap.
--
-- The satellite's symbolic source -> signed-IR -> paired-prime macro layer is
-- already theorem-facing on its closed slices.  Its Python executable uses the
-- standard FRACTRAN policy: scan from the first fraction and apply the first
-- applicable one.  This module isolates the exact generic fact needed to move
-- that policy from regression evidence into a proof receipt.
------------------------------------------------------------------------

variable
  State Rule : Set

------------------------------------------------------------------------
-- Standard first-applicable one-step semantics.
------------------------------------------------------------------------

data FirstApplicableStep
    {State Rule : Set}
    (Applies : State → Rule → Set)
    (apply : State → Rule → State) :
    List Rule → State → State → Set where

  choose-head :
    ∀ {rule rest state} →
    Applies state rule →
    FirstApplicableStep Applies apply
      (rule ∷ rest) state (apply state rule)

  skip-head :
    ∀ {rule rest state next} →
    ¬ (Applies state rule) →
    FirstApplicableStep Applies apply rest state next →
    FirstApplicableStep Applies apply
      (rule ∷ rest) state next

------------------------------------------------------------------------
-- If a prefix is blocked and the next rule applies, the standard interpreter
-- must choose exactly that rule.  This is the abstract theorem behind the
-- Python check `applied_indices == [0,1,...]`.
------------------------------------------------------------------------

PrefixBlocked :
  ∀ {State Rule : Set} →
  (State → Rule → Set) →
  State → List Rule → Set
PrefixBlocked Applies state [] = ⊤
PrefixBlocked Applies state (rule ∷ rest) =
  ¬ (Applies state rule) × PrefixBlocked Applies state rest

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

blockedPrefixChoosesNext :
  ∀ {State Rule : Set}
    {Applies : State → Rule → Set}
    {apply : State → Rule → State}
    {state : State}
    (prefix : List Rule)
    (rule : Rule)
    (suffix : List Rule) →
  PrefixBlocked Applies state prefix →
  Applies state rule →
  FirstApplicableStep Applies apply
    (append prefix (rule ∷ suffix))
    state
    (apply state rule)
blockedPrefixChoosesNext [] rule suffix blocked applies =
  choose-head applies
blockedPrefixChoosesNext (head ∷ tail) rule suffix
    (headBlocked , tailBlocked) applies =
  skip-head headBlocked
    (blockedPrefixChoosesNext tail rule suffix tailBlocked applies)

------------------------------------------------------------------------
-- A concrete paired-prime macro can therefore discharge standard FRACTRAN
-- ordering one intended step at a time.  We keep arithmetic-specific facts in
-- a separate receipt: this theorem does not assume primality/divisibility by
-- definition.
------------------------------------------------------------------------

record IntendedFractionStepReceipt
    {State Rule : Set}
    (Applies : State → Rule → Set)
    (apply : State → Rule → State)
    (program : List Rule)
    (prefix : List Rule)
    (rule : Rule)
    (suffix : List Rule)
    (state target : State) : Set₁ where
  constructor intendedFractionStepReceipt
  field
    programDecomposition :
      program ≡ append prefix (rule ∷ suffix)
    earlierFractionsBlocked :
      PrefixBlocked Applies state prefix
    intendedFractionApplies :
      Applies state rule
    intendedTarget :
      target ≡ apply state rule

open IntendedFractionStepReceipt public

receiptYieldsFirstApplicableStep :
  ∀ {State Rule : Set}
    {Applies : State → Rule → Set}
    {apply : State → Rule → State}
    {program prefix : List Rule}
    {rule : Rule}
    {suffix : List Rule}
    {state target : State} →
  IntendedFractionStepReceipt
    Applies apply program prefix rule suffix state target →
  FirstApplicableStep Applies apply program state target
receiptYieldsFirstApplicableStep receipt
  rewrite programDecomposition receipt
        | intendedTarget receipt
  = blockedPrefixChoosesNext
      _ _ _
      (earlierFractionsBlocked receipt)
      (intendedFractionApplies receipt)

------------------------------------------------------------------------
-- Numeric paired-prime specialization boundary.
--
-- For FRACDASH, `Applies` is denominator divisibility and `apply` is exact
-- integer multiplication/division.  The remaining concrete proof therefore
-- consists of prime-exclusivity/divisibility receipts for each generated macro
-- family, not floating-point error control.
------------------------------------------------------------------------

record FRACDASHNumericInterpreterBoundary : Set where
  constructor fracdashNumericInterpreterBoundary
  field
    firstApplicablePolicyFormalised : Bool
    firstApplicablePolicyFormalisedIsTrue :
      firstApplicablePolicyFormalised ≡ true

    blockedPrefixPlusApplicabilitySelectsIntendedRule : Bool
    blockedPrefixPlusApplicabilitySelectsIntendedRuleIsTrue :
      blockedPrefixPlusApplicabilitySelectsIntendedRule ≡ true

    pythonExactIntegerCheckIsKernelProofByItself : Bool
    pythonExactIntegerCheckIsKernelProofByItselfIsFalse :
      pythonExactIntegerCheckIsKernelProofByItself ≡ false

    remainingGapIsFloatingPointApproximation : Bool
    remainingGapIsFloatingPointApproximationIsFalse :
      remainingGapIsFloatingPointApproximation ≡ false

canonicalFRACDASHNumericInterpreterBoundary :
  FRACDASHNumericInterpreterBoundary
canonicalFRACDASHNumericInterpreterBoundary =
  fracdashNumericInterpreterBoundary
    true refl
    true refl
    false refl
    false refl
