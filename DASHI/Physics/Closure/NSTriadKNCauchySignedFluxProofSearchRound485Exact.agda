module DASHI.Physics.Closure.NSTriadKNCauchySignedFluxProofSearchRound485Exact where

------------------------------------------------------------------------
-- ROUND485 / CORRECTED FIRST-MISSING SEARCH: POSITIVE SIGNED FLUX
--
-- R481 correctly enforced first-missing prerequisite order, but its candidate
-- same-object target used R480's full R477 Cauchy form.  R484 audits that route:
--
--   full = diagonal + offDiagonal
--   offDiagonal = literal R397/R385 signed flux (R448)
--
-- so full cannot be the signed-cross identity target without a diagonal=0
-- receipt.  The repository already owns the ACTUAL representation seam in R448.
-- Therefore the current first missing mathematical node is simply the positive
-- orientation signed-flux allowance.  R458 confirms that exactly this
-- orientation remains open.
--
-- Full-form R477/R478 upper bounds remain admissible sufficient producers, since
-- diagonal nonnegativity gives offDiagonal <= full, but they are not mandatory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Core.QueryPromotionResidualBidiExact as Residual
import DASHI.Physics.Closure.NSTriadKNCauchyTerminalFluxEndpointRound458Exact as R458
import DASHI.Physics.Closure.NSTriadKNCauchyFullVsSignedFluxBoundaryRound484Exact as R484

------------------------------------------------------------------------
-- Correct literal prerequisite state.
------------------------------------------------------------------------

data SignedFluxResidual : Set where
  missingSignedFluxRepresentation : SignedFluxResidual
  missingPositiveSignedFluxAllowance : SignedFluxResidual
  signedFluxConsumerClosed : SignedFluxResidual

record SignedFluxStatus : Set where
  constructor signed-flux-status
  field
    signedFluxRepresentationPresent : Bool
    positiveSignedFluxAllowancePresent : Bool

open SignedFluxStatus public

firstSignedFluxResidual : SignedFluxStatus → SignedFluxResidual
firstSignedFluxResidual (signed-flux-status false payment) =
  missingSignedFluxRepresentation
firstSignedFluxResidual (signed-flux-status true false) =
  missingPositiveSignedFluxAllowance
firstSignedFluxResidual (signed-flux-status true true) =
  signedFluxConsumerClosed

data SignedFluxProducer : Set where
  recoverR448Representation : SignedFluxProducer
  provePositiveSignedFluxAllowance : SignedFluxProducer
  noSignedFluxProducerNeeded : SignedFluxProducer

producerFor : SignedFluxResidual → SignedFluxProducer
producerFor missingSignedFluxRepresentation = recoverR448Representation
producerFor missingPositiveSignedFluxAllowance = provePositiveSignedFluxAllowance
producerFor signedFluxConsumerClosed = noSignedFluxProducerNeeded

data SearchMechanism : Set where
  Look : SearchMechanism
  Think : SearchMechanism
  Done : SearchMechanism

mechanismFor : SignedFluxResidual → SearchMechanism
mechanismFor missingSignedFluxRepresentation = Look
mechanismFor missingPositiveSignedFluxAllowance = Think
mechanismFor signedFluxConsumerClosed = Done

currentSignedFluxStatus : SignedFluxStatus
currentSignedFluxStatus = signed-flux-status true false

currentFirstMissingIsPositiveAllowance :
  firstSignedFluxResidual currentSignedFluxStatus
  ≡ missingPositiveSignedFluxAllowance
currentFirstMissingIsPositiveAllowance = refl

currentProducerIsPositiveAllowanceProof :
  producerFor (firstSignedFluxResidual currentSignedFluxStatus)
  ≡ provePositiveSignedFluxAllowance
currentProducerIsPositiveAllowanceProof = refl

currentMechanismIsThink :
  mechanismFor (firstSignedFluxResidual currentSignedFluxStatus) ≡ Think
currentMechanismIsThink = refl

------------------------------------------------------------------------
-- Learned route dispositions.
------------------------------------------------------------------------

fullFormAsSameObjectDisposition : Least.RouteDisposition
fullFormAsSameObjectDisposition = Least.rejected Least.carrierMismatch

fullFormUpperBoundAsProducerDisposition : Least.RouteDisposition
fullFormUpperBoundAsProducerDisposition = Least.admitted

r448RepresentationDisposition : Least.RouteDisposition
r448RepresentationDisposition = Least.redirectedReuse

------------------------------------------------------------------------
-- Admission certifies route search only, never the analytic payment.
------------------------------------------------------------------------

positiveSignedFluxRouteAdmission : Least.RouteAdmission
positiveSignedFluxRouteAdmission =
  Least.route-admission
    Least.exactTarget
    Least.sameObjectSpine
    Least.prerequisiteClosure
    Least.noKnownNoGo
    Least.noCircularDependency
    Least.noSilentStrengthening
    Least.authorityAdequacy
    Least.noveltyAgainstRepo
    Least.frontierImproves

positiveSignedFluxLiveSearch : Least.LiveProofSearch
positiveSignedFluxLiveSearch = Least.elaborateRoute positiveSignedFluxRouteAdmission

------------------------------------------------------------------------
-- No-collapse boundaries inherited from generic residual semantics.
------------------------------------------------------------------------

genericProducerNameDoesNotCreateReceipt : Residual.ProducerNameCreatesReceipt → ⊥
genericProducerNameDoesNotCreateReceipt = Residual.producerNameDoesNotCreateReceipt

genericLaterStageDoesNotRepairRepresentationGap :
  Residual.LaterStageRepairsEarlierGap → ⊥
genericLaterStageDoesNotRepairRepresentationGap = Residual.laterStageDoesNotRepairEarlierGap

------------------------------------------------------------------------
-- Exact pins to the physical route.
------------------------------------------------------------------------

round485R448RepresentationAlreadyOwned : Bool
round485R448RepresentationAlreadyOwned =
  R484.round484R448IdentifiesLiteralSignedFluxWithOffDiagonal

round485FullFormIdentityRouteRejected : Bool
round485FullFormIdentityRouteRejected = true

round485FullFormUpperBoundRouteRemainsOptionalProducer : Bool
round485FullFormUpperBoundRouteRemainsOptionalProducer = true

round485CurrentFirstMissingIsPositiveSignedFluxAllowance : Bool
round485CurrentFirstMissingIsPositiveSignedFluxAllowance = true

round485CurrentMechanismIsThink : Bool
round485CurrentMechanismIsThink = true

round485PositiveSignedFluxAllowanceClosed : Bool
round485PositiveSignedFluxAllowanceClosed =
  R458.round458PositiveTerminalR397FluxPaid

round485SpacetimeRemainderClosed : Bool
round485SpacetimeRemainderClosed = R458.round458SpacetimeRemainderPaid

round485PackageAClosed : Bool
round485PackageAClosed = false

round485ClayPromotion : Bool
round485ClayPromotion = false

round485PositiveSignedFluxAllowanceClosedIsFalse :
  round485PositiveSignedFluxAllowanceClosed ≡ false
round485PositiveSignedFluxAllowanceClosedIsFalse =
  R458.round458PositiveTerminalR397FluxPaidIsFalse

round485SpacetimeRemainderClosedIsFalse :
  round485SpacetimeRemainderClosed ≡ false
round485SpacetimeRemainderClosedIsFalse =
  R458.round458SpacetimeRemainderPaidIsFalse

round485ClayPromotionIsFalse : round485ClayPromotion ≡ false
round485ClayPromotionIsFalse = refl
