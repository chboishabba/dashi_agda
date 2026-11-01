module DASHI.Physics.Closure.P0SecondaryObligationQueue where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualConsumerNextObligation as W6
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5

------------------------------------------------------------------------
-- W5/W6/W9 cross-lane queue.
--
-- This module is a validation-only queue surface.  It imports the current
-- next-obligation diagnostics for the remaining secondary lanes and keeps
-- them explicitly non-promoting.

data P0SecondaryLane : Set where
  W5GRQFTConsumer : P0SecondaryLane
  W6PNFResidualConsumer : P0SecondaryLane
  W9CancellationPressureCompatibility : P0SecondaryLane

record P0SecondaryObligationQueue : Setω where
  field
    queuedLanes :
      List P0SecondaryLane

    w5GRQFTCurrentStatus :
      W5.GRQFTConsumerNextObligationCurrentStatus

    w6PNFResidualCurrentDiagnostic :
      W6.PNFResidualConsumerMissingReceiptDiagnostic

    w9CancellationPressureRoute :
      W9.W9CompatibilityRoute

    w9CancellationPressureMissingIngredient :
      W9.W9MissingIngredient

    requiredQueueReceipts :
      List String

    validationOnlyBoundary :
      List String

canonicalP0SecondaryObligationQueue :
  P0SecondaryObligationQueue
canonicalP0SecondaryObligationQueue =
  record
    { queuedLanes =
        W5GRQFTConsumer
        ∷ W6PNFResidualConsumer
        ∷ W9CancellationPressureCompatibility
        ∷ []
    ; w5GRQFTCurrentStatus =
        W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; w6PNFResidualCurrentDiagnostic =
        W6.canonicalPNFResidualConsumerMissingReceiptDiagnostic
    ; w9CancellationPressureRoute =
        W9.diagnosticOnly
    ; w9CancellationPressureMissingIngredient =
        W9.missingPressureWitness
    ; requiredQueueReceipts =
        "W5 requires external GR/QFT promotion authority plus GR equation and QFT interaction consumer laws"
        ∷ "W6 requires paired runtime PNF emission receipts and receipt-backed residual computation"
        ∷ "W9 requires either the existing pressure witness or the weighted cancellation-identification seam"
        ∷ []
    ; validationOnlyBoundary =
        "This queue imports W5/W6/W9 current obligation surfaces only"
        ∷ "It does not inhabit GRQFTClosurePromotionAuthorityToken"
        ∷ "It does not construct PNFEmissionReceipt values"
        ∷ "It does not inhabit CancellationPressureCompatibility"
        ∷ "It does not promote GR/QFT, PNF residual, or cancellation-pressure closure"
        ∷ []
    }

queuedP0SecondaryLanes :
  List P0SecondaryLane
queuedP0SecondaryLanes =
  P0SecondaryObligationQueue.queuedLanes
    canonicalP0SecondaryObligationQueue
