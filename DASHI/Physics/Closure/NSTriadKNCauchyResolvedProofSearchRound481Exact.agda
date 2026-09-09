module DASHI.Physics.Closure.NSTriadKNCauchyResolvedProofSearchRound481Exact where

------------------------------------------------------------------------
-- ROUND481 / FIRST-MISSING PROOF SEARCH FOR THE R480 PHYSICAL SNAPSHOT
--
-- Cross-pollination with the repository's generic proof-search discipline:
--
--   * ProofSearchLeastPrivilegeAdmissionExact:
--       exact target + same-object + prerequisite closure before elaboration;
--       theorem/producer names are not proof capabilities.
--
--   * QueryPromotionResidualBidiExact:
--       expose the FIRST missing obligation;
--       later-stage success cannot repair an earlier missing receipt;
--       producer selection does not manufacture a receipt.
--
-- R480 has two literal prerequisites in dependency order:
--
--   1. construct the exact physical Cauchy-resolved snapshot/same-object weld;
--   2. prove the selected resolved inequality on that SAME physical snapshot.
--
-- The second mathematical search is not admitted while the first receipt is
-- missing.  Once an actual R480 proof object exists, downstream R432 payment is
-- a compiler, not a fresh analytic leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Core.QueryPromotionResidualBidiExact as Residual
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedPhysicalSnapshotRound480Exact as R480
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477

------------------------------------------------------------------------
-- Literal R480 prerequisite state.
------------------------------------------------------------------------

data R480Residual : Set where
  missingPhysicalSnapshotWeld : R480Residual
  missingSelectedResolvedPayment : R480Residual
  r480Closed : R480Residual

record R480Status : Set where
  constructor r480-status
  field
    physicalSnapshotWeldPresent : Bool
    selectedResolvedPaymentPresent : Bool

open R480Status public

firstR480Residual : R480Status → R480Residual
firstR480Residual (r480-status false selected) = missingPhysicalSnapshotWeld
firstR480Residual (r480-status true false) = missingSelectedResolvedPayment
firstR480Residual (r480-status true true) = r480Closed

------------------------------------------------------------------------
-- Producer routing is typed but remains non-authoritative until a receipt is
-- constructed.
------------------------------------------------------------------------

data R480Producer : Set where
  constructPhysicalSnapshotWeld : R480Producer
  proveSelectedResolvedPayment : R480Producer
  noR480ProducerNeeded : R480Producer

producerFor : R480Residual → R480Producer
producerFor missingPhysicalSnapshotWeld = constructPhysicalSnapshotWeld
producerFor missingSelectedResolvedPayment = proveSelectedResolvedPayment
producerFor r480Closed = noR480ProducerNeeded

firstR480Producer : R480Status → R480Producer
firstR480Producer status = producerFor (firstR480Residual status)

data SearchMechanism : Set where
  Look : SearchMechanism
  Think : SearchMechanism
  Done : SearchMechanism

mechanismFor : R480Residual → SearchMechanism
mechanismFor missingPhysicalSnapshotWeld = Look
mechanismFor missingSelectedResolvedPayment = Think
mechanismFor r480Closed = Done

firstR480Mechanism : R480Status → SearchMechanism
firstR480Mechanism status = mechanismFor (firstR480Residual status)

------------------------------------------------------------------------
-- Current fail-closed state and exact transition.
------------------------------------------------------------------------

currentR480Status : R480Status
currentR480Status = r480-status false false

currentFirstMissingIsSnapshotWeld :
  firstR480Residual currentR480Status ≡ missingPhysicalSnapshotWeld
currentFirstMissingIsSnapshotWeld = refl

currentProducerIsConstructSnapshot :
  firstR480Producer currentR480Status ≡ constructPhysicalSnapshotWeld
currentProducerIsConstructSnapshot = refl

currentMechanismIsLook :
  firstR480Mechanism currentR480Status ≡ Look
currentMechanismIsLook = refl

afterSnapshotStatus : R480Status
afterSnapshotStatus = r480-status true false

afterSnapshotFirstMissingIsSelectedPayment :
  firstR480Residual afterSnapshotStatus ≡ missingSelectedResolvedPayment
afterSnapshotFirstMissingIsSelectedPayment = refl

afterSnapshotProducerIsAnalyticPayment :
  firstR480Producer afterSnapshotStatus ≡ proveSelectedResolvedPayment
afterSnapshotProducerIsAnalyticPayment = refl

afterSnapshotMechanismIsThink :
  firstR480Mechanism afterSnapshotStatus ≡ Think
afterSnapshotMechanismIsThink = refl

------------------------------------------------------------------------
-- Least-privilege route admission.  This certifies the SEARCH ROUTE only; it
-- does not inhabit either R480 mathematical receipt.
------------------------------------------------------------------------

r480RouteAdmission : Least.RouteAdmission
r480RouteAdmission =
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

r480LiveProofSearch : Least.LiveProofSearch
r480LiveProofSearch = Least.elaborateRoute r480RouteAdmission

------------------------------------------------------------------------
-- Receipt boundary.  Booleans and producer names cannot promote the programme.
-- The ONLY downstream compiler here consumes an actual R480 proof object.
------------------------------------------------------------------------

r480ReceiptPaysR432 :
  ∀ {Index}
    {family : R477.CauchyResolvedCellFamily Index}
    {A} →
  R480.PhysicalResolvedSnapshotPayment family A →
  R432.FixedOutputSignedCrossPayment
r480ReceiptPaysR432 = R480.physicalResolvedSnapshotPaysR432

data ProducerNameCreatesR480Receipt : Set where

data LaterSelectedPaymentRepairsMissingSnapshot : Set where

data BooleanStatusPromotesR432 : Set where

producerNameDoesNotCreateR480Receipt : ProducerNameCreatesR480Receipt → ⊥
producerNameDoesNotCreateR480Receipt ()

laterPaymentDoesNotRepairMissingSnapshot :
  LaterSelectedPaymentRepairsMissingSnapshot → ⊥
laterPaymentDoesNotRepairMissingSnapshot ()

booleanStatusDoesNotPromoteR432 : BooleanStatusPromotesR432 → ⊥
booleanStatusDoesNotPromoteR432 ()

------------------------------------------------------------------------
-- Exact compatibility with generic residual semantics.
------------------------------------------------------------------------

genericProducerNameIsNotReceipt : Residual.ProducerNameCreatesReceipt → ⊥
genericProducerNameIsNotReceipt = Residual.producerNameDoesNotCreateReceipt

genericLaterStageDoesNotRepairEarlierGap :
  Residual.LaterStageRepairsEarlierGap → ⊥
genericLaterStageDoesNotRepairEarlierGap = Residual.laterStageDoesNotRepairEarlierGap

------------------------------------------------------------------------
-- Search ledger.
------------------------------------------------------------------------

round481UsesLeastPrivilegeAdmission : Bool
round481UsesLeastPrivilegeAdmission = true

round481UsesFirstMissingResidualScheduling : Bool
round481UsesFirstMissingResidualScheduling = true

round481CurrentFirstMissingIsSnapshotWeld : Bool
round481CurrentFirstMissingIsSnapshotWeld = true

round481SelectedPaymentSearchCurrentlyAdmitted : Bool
round481SelectedPaymentSearchCurrentlyAdmitted = false

round481AfterSnapshotSelectedPaymentSearchAdmitted : Bool
round481AfterSnapshotSelectedPaymentSearchAdmitted = true

round481ProducerNameIsReceipt : Bool
round481ProducerNameIsReceipt = false

round481BooleanStatusIsReceipt : Bool
round481BooleanStatusIsReceipt = false

round481PhysicalSnapshotWeldClosed : Bool
round481PhysicalSnapshotWeldClosed = false

round481PhysicalSelectedResolvedPaymentClosed : Bool
round481PhysicalSelectedResolvedPaymentClosed = false

round481PackageAClosed : Bool
round481PackageAClosed = false

round481ClayPromotion : Bool
round481ClayPromotion = false

round481SelectedPaymentSearchCurrentlyAdmittedIsFalse :
  round481SelectedPaymentSearchCurrentlyAdmitted ≡ false
round481SelectedPaymentSearchCurrentlyAdmittedIsFalse = refl

round481PhysicalSnapshotWeldClosedIsFalse :
  round481PhysicalSnapshotWeldClosed ≡ false
round481PhysicalSnapshotWeldClosedIsFalse = refl

round481ClayPromotionIsFalse : round481ClayPromotion ≡ false
round481ClayPromotionIsFalse = refl
