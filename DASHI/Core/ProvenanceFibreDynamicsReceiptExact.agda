module DASHI.Core.ProvenanceFibreDynamicsReceiptExact where

------------------------------------------------------------------------
-- EXACT REOPENING TURNS PROVENANCE RECEIPTS INTO FINE-FIBRE COORDINATES
--
-- This is an extension theorem over the existing canonical cores:
--
--   FibrePreservingDynamicsExact
--   ProvenanceBearingQuotient
--
-- It does not introduce another quotient or dynamics abstraction.
--
-- Exact result:
--
--   same surface + same receipt => same fine carrier.
--
-- Hence every nontrivial hidden/fibre-preserving transition must alter the
-- provenance receipt of an exact reopenable quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient

surfaceAndReceiptDetermineCarrier :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core)
    {x y : Fibre.Carrier core} →
  Fibre.project core x ≡ Fibre.project core y →
  Quotient.receipt quotient x ≡ Quotient.receipt quotient y →
  x ≡ y
surfaceAndReceiptDetermineCarrier {core} quotient {x} {y}
  sameSurface sameReceipt =
  trans
    (sym (Quotient.reopenExact quotient x))
    (trans
      (cong
        (λ surface →
          Quotient.reopen quotient surface (Quotient.receipt quotient x))
        sameSurface)
      (trans
        (cong
          (Quotient.reopen quotient (Fibre.project core y))
          sameReceipt)
        (Quotient.reopenExact quotient y)))

surfaceReceiptObserver :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core) →
  Fibre.Carrier core →
  Fibre.Surface core × Quotient.Receipt quotient
surfaceReceiptObserver {core} quotient x =
  Fibre.project core x , Quotient.receipt quotient x

surfaceReceiptObserverSeparating :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core) →
  (x y : Fibre.Carrier core) →
  surfaceReceiptObserver quotient x ≡ surfaceReceiptObserver quotient y →
  x ≡ y
surfaceReceiptObserverSeparating quotient x y same =
  surfaceAndReceiptDetermineCarrier quotient
    (cong proj₁ same)
    (cong proj₂ same)

hiddenTransitionChangesReceipt :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core)
    {operator : Dynamics.CarrierOperator core}
    {x : Fibre.Carrier core} →
  Dynamics.HiddenTransition core operator x →
  Quotient.receipt quotient (operator x)
    ≡ Quotient.receipt quotient x →
  ⊥
hiddenTransitionChangesReceipt quotient hidden sameReceipt =
  Dynamics.fineStateChanges hidden
    (surfaceAndReceiptDetermineCarrier quotient
      (Dynamics.coarseSurfaceStable hidden)
      sameReceipt)

nontrivialFibreAutomorphismChangesReceipt :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core)
    (symmetry : Dynamics.NontrivialFibreAutomorphism core) →
  Quotient.receipt quotient
      (Dynamics.forward
        (Dynamics.automorphism symmetry)
        (Dynamics.movedPoint symmetry))
    ≡ Quotient.receipt quotient (Dynamics.movedPoint symmetry) →
  ⊥
nontrivialFibreAutomorphismChangesReceipt quotient symmetry =
  hiddenTransitionChangesReceipt quotient
    (Dynamics.nontrivialFibreAutomorphismCreatesHiddenTransition symmetry)

record ProvenanceFibreDynamicsReceiptBoundary : Set where
  constructor provenanceFibreDynamicsReceiptBoundary
  field
    surfacePlusReceiptSeparatesExactFineState : Bool
    surfacePlusReceiptSeparatesExactFineStateIsTrue :
      surfacePlusReceiptSeparatesExactFineState ≡ true
    nontrivialHiddenMotionMustChangeReceipt : Bool
    nontrivialHiddenMotionMustChangeReceiptIsTrue :
      nontrivialHiddenMotionMustChangeReceipt ≡ true
    receiptChangePromotesSemanticTruth : Bool
    receiptChangePromotesSemanticTruthIsFalse :
      receiptChangePromotesSemanticTruth ≡ false

canonicalProvenanceFibreDynamicsReceiptBoundary :
  ProvenanceFibreDynamicsReceiptBoundary
canonicalProvenanceFibreDynamicsReceiptBoundary =
  provenanceFibreDynamicsReceiptBoundary
    true refl
    true refl
    false refl
