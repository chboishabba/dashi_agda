module DASHI.Foundations.Base369RelationalSymmetryRealisationExact where

------------------------------------------------------------------------
-- Reusable 3/6/9 relational calculus over an arbitrary symmetry carrier.
-- The ternary observer is context-indexed; it does not require the carrier to
-- have three or nine elements.  Completion is a separate axis from polarity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using (NonaryTruth)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit)
open import DASHI.Foundations.Base369CompletedRelationalDigitExact using
  (CompletionBit; uninstantiated)
open import DASHI.Foundations.Base369NonaryTritSquareExact using
  ( nonaryDigitToHighTrit
  ; nonaryDigitToLowTrit
  ; negateSSPTrit
  ; complementNonaryDigit
  ; complementReversesLowTrit
  )

record RelationalSymmetryRealisation : Set₁ where
  constructor relationalSymmetryRealisation
  field
    SymmetryGroup : Set
    Carrier : Set
    CoarseMode : Set
    CompletionTarget : Set

    act : SymmetryGroup → Carrier → Carrier
    observeMode : Carrier → CoarseMode
    observeTrit : Carrier → SSPTrit
    observeCompletion : Carrier → CompletionBit

    reverse : Carrier → Carrier
    reverseInvolutive :
      (state : Carrier) → reverse (reverse state) ≡ state
    reverseTrit :
      (state : Carrier) →
      observeTrit (reverse state) ≡ negateSSPTrit (observeTrit state)

    complete : Carrier → CompletionTarget
    overflow : CompletionTarget → Carrier

open RelationalSymmetryRealisation public

-- Concrete carrier-level instance for the nonary square.  The unit symmetry
-- group is intentionally trivial here: the exact nontrivial structure is the
-- complement involution and its action on the low SSP trit.
data UnitSymmetry : Set where
  unitSymmetry : UnitSymmetry

nonaryComplementRealisation : RelationalSymmetryRealisation
nonaryComplementRealisation =
  relationalSymmetryRealisation
    UnitSymmetry
    NonaryTruth
    SSPTrit
    NonaryTruth
    (λ _ state → state)
    nonaryDigitToHighTrit
    nonaryDigitToLowTrit
    (λ _ → uninstantiated)
    complementNonaryDigit
    DASHI.Foundations.Base369NonaryTritSquareExact.complementNonaryDigitInvolutive
    complementReversesLowTrit
    (λ state → state)
    (λ state → state)

nonaryRealisationReversesPolarity :
  (state : NonaryTruth) →
  observeTrit nonaryComplementRealisation
    (reverse nonaryComplementRealisation state)
  ≡ negateSSPTrit
      (observeTrit nonaryComplementRealisation state)
nonaryRealisationReversesPolarity =
  reverseTrit nonaryComplementRealisation
