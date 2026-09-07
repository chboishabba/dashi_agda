module DASHI.Physics.Closure.NSTriadKNClayResidualIntrospectionRound509Exact where

------------------------------------------------------------------------
-- ROUND509 / CLAY RESIDUAL INTROSPECTION ON THE LIVE R406 CUTSET
--
-- This owner applies the repository's introspective proof-search discipline to
-- the current two-leaf R406 terminal cut.  It does not invent a new planner and
-- does not count diagrams, candidate lemmas, or route descriptions as payment.
--
-- Physical reading:
--   * leaf A asks whether the exact off-diagonal signed resolvent interaction is
--     uniformly bounded on the literal Galerkin trajectory;
--   * leaf B asks whether the same trajectory satisfies the signed critical
--     production estimate, whose current sharp producer is the external
--     cross-triad forcing payment, followed by an exact remainder weld.
--
-- The two leaves remain independent until an actual theorem identifies them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504
import DASHI.Physics.Closure.NSTriadKNLiteralR406CriticalProductionProofSearchRound508Exact as R508

data ClayResidual509 : Set where
  signedCrossUniformBoundResidual : ClayResidual509
  externalCrossTriadCriticalPaymentResidual : ClayResidual509
  literalR406RemainderWeldResidual : ClayResidual509
  clayCutsetClosed : ClayResidual509

data MissingCoordinate509 : Set where
  cutoffUniformSameOutputSameScaleSignedControl : MissingCoordinate509
  signedExternalCrossTriadForcingControl : MissingCoordinate509
  round104ToLiteralR406SameObjectIdentity : MissingCoordinate509
  noMissingCoordinate : MissingCoordinate509

data Producer509 : Set where
  directResolventSignedSpacetimeEstimate : Producer509
  waleffeExternalCrossTriadSignedEstimate : Producer509
  exactRemainderCarrierWeld : Producer509
  compileExistingTerminalChain : Producer509

missingCoordinateFor : ClayResidual509 → MissingCoordinate509
missingCoordinateFor signedCrossUniformBoundResidual =
  cutoffUniformSameOutputSameScaleSignedControl
missingCoordinateFor externalCrossTriadCriticalPaymentResidual =
  signedExternalCrossTriadForcingControl
missingCoordinateFor literalR406RemainderWeldResidual =
  round104ToLiteralR406SameObjectIdentity
missingCoordinateFor clayCutsetClosed = noMissingCoordinate

producerFor : ClayResidual509 → Producer509
producerFor signedCrossUniformBoundResidual =
  directResolventSignedSpacetimeEstimate
producerFor externalCrossTriadCriticalPaymentResidual =
  waleffeExternalCrossTriadSignedEstimate
producerFor literalR406RemainderWeldResidual =
  exactRemainderCarrierWeld
producerFor clayCutsetClosed = compileExistingTerminalChain

record IntrospectiveState509 : Set where
  constructor introspective-state-509
  field
    residual : ClayResidual509
    missingCoordinate : MissingCoordinate509
    producer : Producer509
    coordinateMatchesResidual : missingCoordinate ≡ missingCoordinateFor residual
    producerMatchesResidual : producer ≡ producerFor residual

open IntrospectiveState509 public

currentNSIntrospectiveState509 : IntrospectiveState509
currentNSIntrospectiveState509 =
  introspective-state-509
    signedCrossUniformBoundResidual
    cutoffUniformSameOutputSameScaleSignedControl
    directResolventSignedSpacetimeEstimate
    refl
    refl

-- If leaf A is paid, introspection moves to the sharpened physical part of leaf
-- B, not directly to the R406 weld and not to Clay closure.
afterSignedCrossPayment509 : IntrospectiveState509
afterSignedCrossPayment509 =
  introspective-state-509
    externalCrossTriadCriticalPaymentResidual
    signedExternalCrossTriadForcingControl
    waleffeExternalCrossTriadSignedEstimate
    refl
    refl

-- Once the physical critical payment exists, the remaining leaf-B operation is
-- the literal same-object remainder weld already isolated by R507/R508.
afterPhysicalCriticalPayment509 : IntrospectiveState509
afterPhysicalCriticalPayment509 =
  introspective-state-509
    literalR406RemainderWeldResidual
    round104ToLiteralR406SameObjectIdentity
    exactRemainderCarrierWeld
    refl
    refl

------------------------------------------------------------------------
-- Cross-check against the live owners.
------------------------------------------------------------------------

currentR504FirstResidualStillSignedCross :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
currentR504FirstResidualStillSignedCross = R504.currentFirstTerminalResidual

currentR508CriticalResidualStillPhysicalPayment :
  R508.firstCriticalProductionResidual R508.currentCriticalProductionStatus
  ≡ R508.missingPhysicalSignedCriticalPayment
currentR508CriticalResidualStillPhysicalPayment =
  R508.currentCriticalProductionResidual

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data VisualizationPaysNSResidualPermission : Set where
data CandidateProducerPaysNSResidualPermission : Set where
data LeafAPaysLeafBPermission : Set where
data ExternalCrossTriadPaymentImpliesR406WeldPermission : Set where

visualizationDoesNotPayNSResidual : VisualizationPaysNSResidualPermission → ⊥
visualizationDoesNotPayNSResidual ()

candidateProducerDoesNotPayNSResidual : CandidateProducerPaysNSResidualPermission → ⊥
candidateProducerDoesNotPayNSResidual ()

leafADoesNotPayLeafB : LeafAPaysLeafBPermission → ⊥
leafADoesNotPayLeafB ()

externalCrossTriadPaymentDoesNotCreateR406Weld :
  ExternalCrossTriadPaymentImpliesR406WeldPermission → ⊥
externalCrossTriadPaymentDoesNotCreateR406Weld ()

------------------------------------------------------------------------
-- Progress ledger: progress means search-space reduction on a live terminal
-- residual, never mere descriptive enrichment.
------------------------------------------------------------------------

round509CurrentResidualCount : Bool
round509CurrentResidualCount = true

round509SearchSpaceReducedByR508 : Bool
round509SearchSpaceReducedByR508 = true

round509NewAnalyticPaymentManufactured : Bool
round509NewAnalyticPaymentManufactured = false

round509ClayPromotion : Bool
round509ClayPromotion = false

round509SearchSpaceReducedByR508IsTrue :
  round509SearchSpaceReducedByR508 ≡ true
round509SearchSpaceReducedByR508IsTrue = refl

round509NewAnalyticPaymentManufacturedIsFalse :
  round509NewAnalyticPaymentManufactured ≡ false
round509NewAnalyticPaymentManufacturedIsFalse = refl

round509ClayPromotionIsFalse : round509ClayPromotion ≡ false
round509ClayPromotionIsFalse = refl
