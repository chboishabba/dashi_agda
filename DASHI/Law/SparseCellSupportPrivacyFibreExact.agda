module DASHI.Law.SparseCellSupportPrivacyFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Sparse-cell support is itself a fibre.  Suppression, structural zero,
-- sampling zero and observed zero must not collapse.
------------------------------------------------------------------------

data ZeroKind : Set where
  structuralZero samplingZero observedPositive zeroKindUnresolved : ZeroKind

data SuppressionState : Set where
  notSuppressed privacySuppressed otherSuppressed suppressionUnresolved : SuppressionState

data SupportAdequacy : Set where
  supportAdequate supportSparse supportUnknown : SupportAdequacy

record CellSupportFibre : Set where
  constructor cellSupportFibre
  field
    observedCount : ℕ
    missingCount : ℕ
    suppressedCountLower : ℕ
    suppressedCountUpper : ℕ
    zeroKind : ZeroKind
    suppression : SuppressionState
    adequacy : SupportAdequacy
    supportReference : String

open CellSupportFibre public

canonicalPrivacySuppressedCell : CellSupportFibre
canonicalPrivacySuppressedCell = cellSupportFibre
  0 0 1 4 zeroKindUnresolved privacySuppressed supportUnknown
  "synthetic privacy-suppressed cell: exact count hidden within bounded range"

canonicalObservedZeroCell : CellSupportFibre
canonicalObservedZeroCell = cellSupportFibre
  0 0 0 0 samplingZero notSuppressed supportSparse
  "synthetic observed zero with sampling-zero classification"

canonicalStructuralZeroCell : CellSupportFibre
canonicalStructuralZeroCell = cellSupportFibre
  0 0 0 0 structuralZero notSuppressed supportAdequate
  "synthetic structurally impossible cell"

------------------------------------------------------------------------
-- BIDI consumers require different producers.
------------------------------------------------------------------------

data SparseCellClaim : Set where
  exactCellCount
  cellIsStructuralZero
  noInteractionInCell
  privacySafeAggregate : SparseCellClaim

data SparseCellProducer : Set where
  unsuppressedCellCountProducer
  structuralZeroReceipt
  interactionSupportProducer
  disclosureControlReceipt : SparseCellProducer

reverseSparseCell : SparseCellClaim → SparseCellProducer
reverseSparseCell exactCellCount = unsuppressedCellCountProducer
reverseSparseCell cellIsStructuralZero = structuralZeroReceipt
reverseSparseCell noInteractionInCell = interactionSupportProducer
reverseSparseCell privacySafeAggregate = disclosureControlReceipt

record SparseCellBoundary : Set where
  constructor sparseCellBoundary
  field
    suppressedMeansZero : Bool
    suppressedMeansZeroIsFalse : suppressedMeansZero ≡ false
    unobservedMeansImpossible : Bool
    unobservedMeansImpossibleIsFalse : unobservedMeansImpossible ≡ false
    sparseCellMeansNoInteraction : Bool
    sparseCellMeansNoInteractionIsFalse : sparseCellMeansNoInteraction ≡ false
    structuralZeroEqualsSamplingZero : Bool
    structuralZeroEqualsSamplingZeroIsFalse : structuralZeroEqualsSamplingZero ≡ false

canonicalSparseCellBoundary : SparseCellBoundary
canonicalSparseCellBoundary =
  sparseCellBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Suppressed exact counts become identified intervals rather than zeros.
------------------------------------------------------------------------

record SuppressedCountBounds : Set where
  constructor suppressedCountBounds
  field
    lower upper : ℕ
    boundsReference : String

open SuppressedCountBounds public

countBounds : CellSupportFibre → SuppressedCountBounds
countBounds c with suppression c
... | privacySuppressed = suppressedCountBounds
  (suppressedCountLower c)
  (suppressedCountUpper c)
  (supportReference c)
... | otherSuppressed = suppressedCountBounds
  (suppressedCountLower c)
  (suppressedCountUpper c)
  (supportReference c)
... | _ = suppressedCountBounds
  (observedCount c)
  (observedCount c)
  (supportReference c)

canonicalSuppressedLower : lower (countBounds canonicalPrivacySuppressedCell) ≡ 1
canonicalSuppressedLower = refl

canonicalSuppressedUpper : upper (countBounds canonicalPrivacySuppressedCell) ≡ 4
canonicalSuppressedUpper = refl
