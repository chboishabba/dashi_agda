module DASHI.Physics.Closure.CancellationPressureRetargetConsumerSourceDiagnostic where

-- W9g: current-source diagnostic for W9f's retarget consumer obligation.
--
-- This module records source availability only.  It imports the W9 retarget
-- receipt and W9f consumer-obligation surface, but it does not construct a
-- RetargetConsumerInterface, a consumer acceptance receipt, a canonical Qcore,
-- an admissible quadratic, or CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f

data RetargetConsumerSourcePresence : Set where
  sourcePresent :
    RetargetConsumerSourcePresence
  sourceMissing :
    RetargetConsumerSourcePresence

data RetargetConsumerSourceMissingField : Set where
  missingRetargetConsumerInterfaceSource :
    RetargetConsumerSourceMissingField
  missingCancellationPressureRetargetConsumerAcceptanceReceiptSource :
    RetargetConsumerSourceMissingField

data RetargetConsumerSourceClosureToken : Set where

currentRetargetConsumerSourceMissingFields :
  List RetargetConsumerSourceMissingField
currentRetargetConsumerSourceMissingFields =
  missingRetargetConsumerInterfaceSource
  ∷ missingCancellationPressureRetargetConsumerAcceptanceReceiptSource
  ∷ []

record CancellationPressureRetargetConsumerSourceDiagnostic : Setω where
  field
    retargetReceipt :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt

    selectedNextRoute :
      W9.W9NextTypedRoute

    selectedNextRouteIsCanonicalRetarget :
      selectedNextRoute
      ≡
      W9.supplyPressureCompatibleTargetWithQcoreBoundary

    retargetConsumerInterfaceSource :
      RetargetConsumerSourcePresence

    acceptanceReceiptSource :
      RetargetConsumerSourcePresence

    missingSourceFields :
      List RetargetConsumerSourceMissingField

    obligationMissingFields :
      List W9f.RetargetConsumerMissingField

    obligationMissingFieldsMatchW9f :
      obligationMissingFields
      ≡
      W9f.missingDownstreamConsumerAcceptance
      ∷ W9f.missingTheoremConsumerRouteChange
      ∷ []

    preservedBoundaries :
      List W9f.RetargetConsumerBoundary

    preservedBoundariesMatchW9f :
      preservedBoundaries
      ≡
      W9f.pressureCompatibleButNonQcore
      ∷ W9f.noAdmissibleQuadraticPromotion
      ∷ W9f.noCancellationPressureCompatibilityPromotion
      ∷ []

    requiredInterface :
      String

    requiredReceipt :
      String

    closureWouldNeedInterface :
      RetargetConsumerSourceClosureToken →
      W9f.RetargetConsumerInterface

    diagnosticBoundary :
      List String

    blockerImpact :
      List String

currentCancellationPressureRetargetConsumerSourceDiagnostic :
  CancellationPressureRetargetConsumerSourceDiagnostic
currentCancellationPressureRetargetConsumerSourceDiagnostic =
  record
    { retargetReceipt =
        W9.canonicalPairPressureRetargetReceipt
    ; selectedNextRoute =
        W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.selectedNextRoute
          W9.canonicalPairPressureRetargetReceipt
    ; selectedNextRouteIsCanonicalRetarget =
        refl
    ; retargetConsumerInterfaceSource =
        sourceMissing
    ; acceptanceReceiptSource =
        sourceMissing
    ; missingSourceFields =
        currentRetargetConsumerSourceMissingFields
    ; obligationMissingFields =
        W9f.missingDownstreamConsumerAcceptance
        ∷ W9f.missingTheoremConsumerRouteChange
        ∷ []
    ; obligationMissingFieldsMatchW9f =
        refl
    ; preservedBoundaries =
        W9f.pressureCompatibleButNonQcore
        ∷ W9f.noAdmissibleQuadraticPromotion
        ∷ W9f.noCancellationPressureCompatibilityPromotion
        ∷ []
    ; preservedBoundariesMatchW9f =
        refl
    ; requiredInterface =
        "RetargetConsumerInterface"
    ; requiredReceipt =
        "CancellationPressureRetargetConsumerAcceptanceReceipt"
    ; closureWouldNeedInterface =
        λ ()
    ; diagnosticBoundary =
        "W9f names the downstream retarget consumer obligation, but this source scan found no in-repo RetargetConsumerInterface source"
        ∷ "This source scan found no in-repo CancellationPressureRetargetConsumerAcceptanceReceipt source for canonicalPairPressureRetargetReceipt"
        ∷ "The available W9 receipt remains pressure-compatible at the boundary but non-Qcore"
        ∷ "No admissible-quadratic or CancellationPressureCompatibility promotion is constructed here"
        ∷ []
    ; blockerImpact =
        "Strict blocker remains: W9 retarget cannot replace or route around existing theorem consumers yet"
        ∷ "Missing source fields are RetargetConsumerInterface and CancellationPressureRetargetConsumerAcceptanceReceipt"
        ∷ "The next admissible move is a downstream consumer source plus acceptance receipt, or an explicit theorem route change"
        ∷ []
    }
