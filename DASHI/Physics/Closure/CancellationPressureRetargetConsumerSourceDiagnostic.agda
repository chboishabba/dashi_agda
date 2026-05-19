module DASHI.Physics.Closure.CancellationPressureRetargetConsumerSourceDiagnostic where

-- W9g: current-source diagnostic for W9f's retarget consumer obligation.
--
-- This module records source availability only.  It imports the W9 retarget
-- receipt, W9f consumer-obligation surface, and the weighted-support retarget
-- acceptance receipt, but it does not construct a theorem-consumer route
-- change, a canonical Qcore, an admissible quadratic, or
-- CancellationPressureCompatibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f
import DASHI.Physics.Closure.W9WeightedSupportRetargetConsumerReceipt as W9r

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

data Dim15DeltaToQuadraticFirstMissingStatus : Set where
  dim15DeltaToQuadraticFirstMissing :
    Dim15DeltaToQuadraticFirstMissingStatus

data Dim15DeltaToQuadraticSurvivingRoute : Set where
  supplyDim15TheoremPressureWitness :
    Dim15DeltaToQuadraticSurvivingRoute
  supplyTheoremConsumerRouteChangeForAcceptedRetarget :
    Dim15DeltaToQuadraticSurvivingRoute

canonicalDim15DeltaToQuadraticSurvivingRoutes :
  List Dim15DeltaToQuadraticSurvivingRoute
canonicalDim15DeltaToQuadraticSurvivingRoutes =
  supplyDim15TheoremPressureWitness
  ∷ supplyTheoremConsumerRouteChangeForAcceptedRetarget
  ∷ []

currentRetargetConsumerSourceMissingFields :
  List RetargetConsumerSourceMissingField
currentRetargetConsumerSourceMissingFields =
  []

currentRetargetConsumerObligationMissingFields :
  List W9f.RetargetConsumerMissingField
currentRetargetConsumerObligationMissingFields =
  W9f.missingTheoremConsumerRouteChange
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

    obligationMissingFieldsAreCurrent :
      obligationMissingFields
      ≡
      currentRetargetConsumerObligationMissingFields

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
        sourcePresent
    ; acceptanceReceiptSource =
        sourcePresent
    ; missingSourceFields =
        currentRetargetConsumerSourceMissingFields
    ; obligationMissingFields =
        currentRetargetConsumerObligationMissingFields
    ; obligationMissingFieldsAreCurrent =
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
        "W9WeightedSupportRetargetConsumerReceipt supplies the in-repo RetargetConsumerInterface source"
        ∷ "W9WeightedSupportRetargetConsumerReceipt supplies the in-repo CancellationPressureRetargetConsumerAcceptanceReceipt source for canonicalPairPressureRetargetReceipt"
        ∷ "That acceptance is the weightedMaxPressure <= weightedSupport bound"
        ∷ "The available W9 retarget remains pressure-compatible at the boundary but non-Qcore"
        ∷ "No admissible-quadratic or CancellationPressureCompatibility promotion is constructed here"
        ∷ []
    ; blockerImpact =
        "Strict blocker remains: the accepted W9 retarget cannot replace or route around existing theorem consumers without a theorem-consumer route change"
        ∷ "The retarget consumer interface and acceptance receipt are present but non-promoting"
        ∷ "The next admissible move is an explicit theorem route change, or the original pressure-witness equality/identification route"
        ∷ []
    }

record W9RetargetConsumerLeReceiptDiagnostic : Setω where
  field
    sourceDiagnostic :
      CancellationPressureRetargetConsumerSourceDiagnostic

    weightedSupportRetargetReceipt :
      W9r.WeightedSupportRetargetConsumerReceipt

    retargetConsumerInterfaceSourceIsPresent :
      CancellationPressureRetargetConsumerSourceDiagnostic.retargetConsumerInterfaceSource
        sourceDiagnostic
      ≡
      sourcePresent

    acceptanceReceiptSourceIsPresent :
      CancellationPressureRetargetConsumerSourceDiagnostic.acceptanceReceiptSource
        sourceDiagnostic
      ≡
      sourcePresent

    missingSourceFieldsAreCurrent :
      CancellationPressureRetargetConsumerSourceDiagnostic.missingSourceFields
        sourceDiagnostic
      ≡
      currentRetargetConsumerSourceMissingFields

    retargetConsumer :
      W9f.RetargetConsumerInterface

    acceptanceReceipt :
      W9f.CancellationPressureRetargetConsumerAcceptanceReceipt
        retargetConsumer
        W9.canonicalPairPressureRetargetReceipt

    acceptanceScopeIsRetargetOnly :
      W9r.WeightedSupportRetargetConsumerReceipt.receiptScope
        weightedSupportRetargetReceipt
      ≡
      W9r.retargetConsumerAcceptedOnly

    selectedRouteRemainsRetarget :
      CancellationPressureRetargetConsumerSourceDiagnostic.selectedNextRoute
        sourceDiagnostic
      ≡
      W9.supplyPressureCompatibleTargetWithQcoreBoundary

    preservedBoundariesMatchW9f :
      CancellationPressureRetargetConsumerSourceDiagnostic.preservedBoundaries
        sourceDiagnostic
      ≡
      W9f.pressureCompatibleButNonQcore
      ∷ W9f.noAdmissibleQuadraticPromotion
      ∷ W9f.noCancellationPressureCompatibilityPromotion
      ∷ []

    receiptBoundary :
      List String

currentW9RetargetConsumerLeReceiptDiagnostic :
  W9RetargetConsumerLeReceiptDiagnostic
currentW9RetargetConsumerLeReceiptDiagnostic =
  record
    { sourceDiagnostic =
        currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; weightedSupportRetargetReceipt =
        W9r.canonicalWeightedSupportRetargetConsumerReceipt
    ; retargetConsumerInterfaceSourceIsPresent =
        refl
    ; acceptanceReceiptSourceIsPresent =
        refl
    ; missingSourceFieldsAreCurrent =
        refl
    ; retargetConsumer =
        W9r.weightedSupportRetargetConsumer
    ; acceptanceReceipt =
        W9r.weightedSupportRetargetAcceptanceReceipt
    ; acceptanceScopeIsRetargetOnly =
        refl
    ; selectedRouteRemainsRetarget =
        refl
    ; preservedBoundariesMatchW9f =
        refl
    ; receiptBoundary =
        "Planck W9 scan found a local weighted-support RetargetConsumerInterface inhabitant"
        ∷ "Planck W9 scan found a local CancellationPressureRetargetConsumerAcceptanceReceipt inhabitant for canonicalPairPressureRetargetReceipt"
        ∷ "The acceptance predicate is weightedMaxPressure <= weightedSupport"
        ∷ "The selected pressure-compatible retarget remains non-Qcore and non-promoting"
        ∷ "W9 still requires an explicit theorem-consumer route change or the original equality route"
        ∷ []
    }

record Dim15DeltaToQuadraticObligation : Setω where
  field
    firstMissingStatus :
      Dim15DeltaToQuadraticFirstMissingStatus

    closureObstruction :
      W9.Dim15DeltaToQuadraticClosureObstruction

    closureStatusIsCurrent :
      W9.Dim15DeltaToQuadraticClosureObstruction.closureStatus
        closureObstruction
      ≡
      W9.dim15RoutesExhaustedRetargetAwaitingConsumer

    retargetLeReceiptDiagnostic :
      W9RetargetConsumerLeReceiptDiagnostic

    retargetConsumerInterfaceSourceIsPresent :
      CancellationPressureRetargetConsumerSourceDiagnostic.retargetConsumerInterfaceSource
        (W9RetargetConsumerLeReceiptDiagnostic.sourceDiagnostic
          retargetLeReceiptDiagnostic)
      ≡
      sourcePresent

    acceptanceReceiptSourceIsPresent :
      CancellationPressureRetargetConsumerSourceDiagnostic.acceptanceReceiptSource
        (W9RetargetConsumerLeReceiptDiagnostic.sourceDiagnostic
          retargetLeReceiptDiagnostic)
      ≡
      sourcePresent

    survivingRoutes :
      List Dim15DeltaToQuadraticSurvivingRoute

    survivingRoutesAreCanonical :
      survivingRoutes
      ≡
      canonicalDim15DeltaToQuadraticSurvivingRoutes

    exactSurvivingRouteNames :
      List String

    noPromotionBoundary :
      List String

    nextTheoremAttempt :
      String

currentDim15DeltaToQuadraticObligation :
  Dim15DeltaToQuadraticObligation
currentDim15DeltaToQuadraticObligation =
  record
    { firstMissingStatus =
        dim15DeltaToQuadraticFirstMissing
    ; closureObstruction =
        W9.canonical15DeltaToQuadraticClosureObstruction
    ; closureStatusIsCurrent =
        refl
    ; retargetLeReceiptDiagnostic =
        currentW9RetargetConsumerLeReceiptDiagnostic
    ; retargetConsumerInterfaceSourceIsPresent =
        refl
    ; acceptanceReceiptSourceIsPresent =
        refl
    ; survivingRoutes =
        canonicalDim15DeltaToQuadraticSurvivingRoutes
    ; survivingRoutesAreCanonical =
        refl
    ; exactSurvivingRouteNames =
        "dim-15 theorem: supply a pressure witness accepted by the existing DeltaToQuadraticBridgeTheorem/CancellationPressureCompatibility consumer path"
        ∷ "accepted retarget route: supply an explicit theorem-consumer route change for the non-Qcore weighted-support retarget"
        ∷ []
    ; noPromotionBoundary =
        "This obligation does not construct a dim-15 theorem or pressureWitness"
        ∷ "This obligation records the weighted-support RetargetConsumerInterface and acceptance receipt as present"
        ∷ "This obligation does not construct a theorem-consumer route change"
        ∷ "This obligation does not promote CancellationPressureCompatibility or W9KillReceipt"
        ∷ []
    ; nextTheoremAttempt =
        "Attempt a dim-15-specific pressureWitness over canonicalDeltaTransport; otherwise add a theorem-consumer route change for the accepted non-Qcore retarget"
    }
