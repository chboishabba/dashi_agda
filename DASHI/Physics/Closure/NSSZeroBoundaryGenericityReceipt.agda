module DASHI.Physics.Closure.NSSZeroBoundaryGenericityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed route ledger for the S-zero / genericity surface around the
-- delta1 gate.
--
-- This module records the carrier-side statements only:
--   * {S = 0} is treated as a subset of dOmega_K;
--   * the generic-transversality route is recorded as the route by which
--     {S = 0} should be generically empty for smooth incompressible flows;
--   * the delta1 gate remains a context marker only;
--   * theorem and promotion flags stay false.
--
-- This is a ledger, not a proof. It does not discharge any transversality,
-- emptiness, or promotion obligation.

data NSSZeroBoundaryGenericityLedgerRow : Set where
  sZeroSubsetOfDOmegaKRecorded :
    NSSZeroBoundaryGenericityLedgerRow

  genericTransversalityRouteRecorded :
    NSSZeroBoundaryGenericityLedgerRow

  genericEmptinessForSmoothIncompressibleFlowsRecorded :
    NSSZeroBoundaryGenericityLedgerRow

  delta1GateContextOnlyRecorded :
    NSSZeroBoundaryGenericityLedgerRow

  theoremPromotionFalseRecorded :
    NSSZeroBoundaryGenericityLedgerRow

  clayPromotionFalseRecorded :
    NSSZeroBoundaryGenericityLedgerRow

canonicalNSSZeroBoundaryGenericityLedgerRows :
  List NSSZeroBoundaryGenericityLedgerRow
canonicalNSSZeroBoundaryGenericityLedgerRows =
  sZeroSubsetOfDOmegaKRecorded
  ∷ genericTransversalityRouteRecorded
  ∷ genericEmptinessForSmoothIncompressibleFlowsRecorded
  ∷ delta1GateContextOnlyRecorded
  ∷ theoremPromotionFalseRecorded
  ∷ clayPromotionFalseRecorded
  ∷ []

record NSSZeroBoundaryGenericityReceipt : Set where
  field
    subsetCarrierStatement :
      String

    genericTransversalityStatement :
      String

    genericEmptinessStatement :
      String

    delta1GateStatement :
      String

    ledgerRows :
      List NSSZeroBoundaryGenericityLedgerRow

    ledgerRowsIsCanonical :
      ledgerRows ≡ canonicalNSSZeroBoundaryGenericityLedgerRows

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

open NSSZeroBoundaryGenericityReceipt public

canonicalNSSZeroBoundaryGenericityReceipt :
  NSSZeroBoundaryGenericityReceipt
canonicalNSSZeroBoundaryGenericityReceipt =
  record
    { subsetCarrierStatement =
        "{S=0} subset dOmega_K"
    ; genericTransversalityStatement =
        "Generic-transversality route recorded: for smooth incompressible flows, {S=0} is expected to be generically empty."
    ; genericEmptinessStatement =
        "The generic-emptiness claim is carried as a route ledger only; no formal transversality proof is discharged here."
    ; delta1GateStatement =
        "The delta1 gate is kept as a context marker only, with no promotion or theorem discharge attached to this receipt."
    ; ledgerRows =
        canonicalNSSZeroBoundaryGenericityLedgerRows
    ; ledgerRowsIsCanonical =
        refl
    ; theoremPromotion =
        false
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    }
