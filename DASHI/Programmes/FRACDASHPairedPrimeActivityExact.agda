module DASHI.Programmes.FRACDASHPairedPrimeActivityExact where

open import DASHI.Core.Prelude
import DASHI.Programmes.FRACDASHNumericInterpreterTargetExact as Numeric

------------------------------------------------------------------------
-- Same-object adapter for the FRACDASH numeric paired-prime seam.
--
-- The satellite symbolic compiler reasons in terms of the active PrimeTag in a
-- register.  The standard numeric FRACTRAN interpreter reasons in terms of
-- denominator applicability/divisibility.  `NumericPairedPrimeSelection.agda`
-- in FRACDASH isolates the arithmetic equivalence between those views.
--
-- This owner connects that equivalence directly to #636's existing
-- first-applicable theorem.  The concrete Nat prime arithmetic is intentionally
-- still an input; once supplied, there is no further compiler-selection glue.
------------------------------------------------------------------------

record PairedPrimeActivityInterface : Set₁ where
  constructor pairedPrimeActivityInterface
  field
    State Rule Tag : Set
    applies : State → Rule → Set
    apply : State → Rule → State
    denominatorTag : Rule → Tag
    Active : State → Tag → Set

    applicableImpliesActive :
      ∀ state rule →
      applies state rule →
      Active state (denominatorTag rule)

    activeImpliesApplicable :
      ∀ state rule →
      Active state (denominatorTag rule) →
      applies state rule

open PairedPrimeActivityInterface public

record ActivePrefixSelectionReceipt
    (interface : PairedPrimeActivityInterface)
    (state : State interface)
    (prefix : List (Rule interface))
    (intended : Rule interface) : Set₁ where
  constructor activePrefixSelectionReceipt
  field
    earlierInactive :
      (rule : Rule interface) →
      rule ∈ prefix →
      Active interface state (denominatorTag interface rule) → ⊥

    intendedActive :
      Active interface state (denominatorTag interface intended)

open ActivePrefixSelectionReceipt public

inactiveListGivesBlockedPrefix :
  (interface : PairedPrimeActivityInterface) →
  (state : State interface) →
  (prefix : List (Rule interface)) →
  ((rule : Rule interface) →
    rule ∈ prefix →
    Active interface state (denominatorTag interface rule) → ⊥) →
  Numeric.PrefixBlocked (applies interface) state prefix
inactiveListGivesBlockedPrefix interface state [] inactive = tt
inactiveListGivesBlockedPrefix interface state (rule ∷ rest) inactive =
  (λ appliesRule →
      inactive rule (Data.List.Membership.Propositional.here refl)
        (applicableImpliesActive interface state rule appliesRule))
  ,
  inactiveListGivesBlockedPrefix interface state rest
    (λ later laterInRest →
      inactive later
        (Data.List.Membership.Propositional.there laterInRest))

activityReceiptYieldsFirstApplicableStep :
  (interface : PairedPrimeActivityInterface) →
  (state : State interface) →
  (prefix : List (Rule interface)) →
  (intended : Rule interface) →
  (suffix : List (Rule interface)) →
  ActivePrefixSelectionReceipt interface state prefix intended →
  Numeric.FirstApplicableStep
    (applies interface)
    (apply interface)
    (Numeric.append prefix (intended ∷ suffix))
    state
    (apply interface state intended)
activityReceiptYieldsFirstApplicableStep
    interface state prefix intended suffix receipt =
  Numeric.blockedPrefixChoosesNext
    prefix intended suffix
    (inactiveListGivesBlockedPrefix
      interface state prefix (earlierInactive receipt))
    (activeImpliesApplicable
      interface state intended (intendedActive receipt))

record FRACDASHPairedPrimeActivityBoundary : Set where
  constructor fracdashPairedPrimeActivityBoundary
  field
    activeTagReceiptFeedsFirstApplicableTheorem : Bool
    activeTagReceiptFeedsFirstApplicableTheoremIsTrue :
      activeTagReceiptFeedsFirstApplicableTheorem ≡ true

    concreteNatDivisibilityIffActiveTagClosedHere : Bool
    concreteNatDivisibilityIffActiveTagClosedHereIsFalse :
      concreteNatDivisibilityIffActiveTagClosedHere ≡ false

canonicalFRACDASHPairedPrimeActivityBoundary :
  FRACDASHPairedPrimeActivityBoundary
canonicalFRACDASHPairedPrimeActivityBoundary =
  fracdashPairedPrimeActivityBoundary
    true refl
    false refl
