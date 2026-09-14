module DASHI.Interop.SLRAppendOnlyActiveResidualFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire

------------------------------------------------------------------------
-- APPEND-ONLY ACTIVE RESIDUAL FRONTIER
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-world-store
--
-- Historical GAP1/OBL1 rows are never deleted or rewritten. PAY1 is a
-- first-class SLRW kind-8 evidence receipt whose aux coordinate names the
-- exact residual row it pays. The active frontier is a derived read view:
-- retain the newest observation of a residual unless a same-or-later PAY1
-- targets it. An earlier payment cannot erase a genuinely later reopening.
------------------------------------------------------------------------

paymentWorldWireKindTag : Nat
paymentWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.payment

record ResidualObservation : Set where
  constructor residualObservation
  field
    residualReference : String
    iterationIndex : Nat

open ResidualObservation public

record ResidualPayment : Set where
  constructor residualPayment
  field
    paymentReference : String
    targetResidualReference : String
    iterationIndex : Nat
    paymentMagicIsPAY1 : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ResidualPayment public

record ActiveResidualFrontierParity : Set where
  constructor activeResidualFrontierParity
  field
    paymentKindTagIsEight : Bool
    historicalGapRowsRetained : Bool
    historicalObligationRowsRetained : Bool
    paymentRowsStoredSeparately : Bool
    targetResidualCoordinateIndexed : Bool
    newestResidualObservationSelected : Bool
    sameOrLaterPaymentSuppressesActiveResidual : Bool
    earlierPaymentSuppressesLaterReopening : Bool
    frontierDerivedWithoutUpdate : Bool
    frontierDerivedWithoutDelete : Bool
    frontierStreamsBinaryRows : Bool
    postgresCreatesSemanticAuthority : Bool
    paymentCreatesClaimTruth : Bool
    semanticPromotion : Bool

open ActiveResidualFrontierParity public

canonicalActiveResidualFrontierParity : ActiveResidualFrontierParity
canonicalActiveResidualFrontierParity =
  activeResidualFrontierParity
    true true true true true true true false
    true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HistoricalResidualDeletedAfterPayment : Set where
data EarlierPaymentErasesLaterReopening : Set where
data PaymentCreatesClaimTruth : Set where
data PostgresCreatesResidualAuthority : Set where

historicalResidualCannotBeDeletedAfterPayment : HistoricalResidualDeletedAfterPayment → ⊥
historicalResidualCannotBeDeletedAfterPayment ()

earlierPaymentCannotEraseLaterReopening : EarlierPaymentErasesLaterReopening → ⊥
earlierPaymentCannotEraseLaterReopening ()

paymentDoesNotCreateClaimTruth : PaymentCreatesClaimTruth → ⊥
paymentDoesNotCreateClaimTruth ()

postgresDoesNotCreateResidualAuthority : PostgresCreatesResidualAuthority → ⊥
postgresDoesNotCreateResidualAuthority ()
