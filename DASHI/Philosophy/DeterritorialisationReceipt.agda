module DASHI.Philosophy.DeterritorialisationReceipt where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Every release from one grammar introduces or exposes another organisation.
-- Deterritorialisation therefore carries a reterritorialisation receipt.

record ReconfigurationReceipt
       (Constraint Possibility : Set) : Set₁ where
  field
    removedConstraint :
      Constraint

    introducedConstraint :
      Constraint

    expandedPossibility :
      Possibility

    foreclosedPossibility :
      Possibility

    releasedFromDomination :
      Set

    exposedToNewCapture :
      Set

open ReconfigurationReceipt public

record DeterritorialisationBoundary : Set where
  constructor mkDeterritorialisationBoundary
  field
    crossingBoundariesCanExpandPossibility :
      Bool

    everyDeterritorialisationIsEmancipatory :
      Bool

    reterritorialisationMustBeTracked :
      Bool

    newCaptureCanOccur :
      Bool

open DeterritorialisationBoundary public

canonicalDeterritorialisationBoundary :
  DeterritorialisationBoundary
canonicalDeterritorialisationBoundary =
  mkDeterritorialisationBoundary
    true
    false
    true
    true

canonicalDeterritorialisationNotAutomaticallyEmancipatory :
  everyDeterritorialisationIsEmancipatory
    canonicalDeterritorialisationBoundary
  ≡
  false
canonicalDeterritorialisationNotAutomaticallyEmancipatory =
  refl
