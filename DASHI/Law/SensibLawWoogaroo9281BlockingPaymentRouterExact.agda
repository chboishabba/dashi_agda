module DASHI.Law.SensibLawWoogaroo9281BlockingPaymentRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Evidence
import DASHI.Law.SensibLawWoogaroo9281SourceDerivedSpatialOverlapExact as P3
import DASHI.Law.SensibLawWoogarooEPBC8575BlockingCutsetExecutionStateExact as Cutset

------------------------------------------------------------------------
-- 9281 BLOCKING PAYMENT ROUTER
--
-- This owner composes existing Woogaroo receipts into the smallest current
-- preservation cut.  It creates no new source authority and no legal opinion.
-- Acquisition may occur out of dependency order, but promotion to a
-- counsel-ready execution question may not skip literal instrument identity,
-- same-action / same-phase identity, authoritative geometry, imminence, or the
-- standing / procedural review which belongs with counsel.
------------------------------------------------------------------------

data BlockingPaymentCoordinate : Set where
  condition6aLiteralSubmissionCoordinate : BlockingPaymentCoordinate
  samePhasePreclearanceCoordinate : BlockingPaymentCoordinate
  authoritativeGeometryCoordinate : BlockingPaymentCoordinate
  imminenceCoordinate : BlockingPaymentCoordinate
  standingCounselCoordinate : BlockingPaymentCoordinate

data BlockingPaymentStatus : Set where
  paymentOpen : BlockingPaymentStatus
  investigativeReceiptOnly : BlockingPaymentStatus
  primaryPaymentPaid : BlockingPaymentStatus

record BlockingPayment : Set where
  constructor blocking-payment
  field
    coordinate : BlockingPaymentCoordinate
    status : BlockingPaymentStatus
    exactObject : String
    primaryManifestationRequired : Bool
    sameActionOrPhaseRequired : Bool
    mayPayCounselEscalation : Bool
    mayPayLegalConclusion : Bool

open BlockingPayment public

condition6aLiteralSubmissionPayment : BlockingPayment
condition6aLiteralSubmissionPayment = blocking-payment
  condition6aLiteralSubmissionCoordinate
  paymentOpen
  "Literal 9281/2024/OW condition 6(a) submission plus Council receipt/acceptance record identifying the Commonwealth instrument or DCCEEW no-controlled-action evidence actually relied upon."
  true true true false

samePhasePreclearancePayment : BlockingPayment
samePhasePreclearancePayment = blocking-payment
  samePhasePreclearanceCoordinate
  paymentOpen
  "Signed stage-specific Environmental Pre-Clearance Checklist/Package and matching pre-start/fauna records for the clearing phase presently at issue."
  true true true false

authoritativeGeometryPayment : BlockingPayment
authoritativeGeometryPayment = blocking-payment
  authoritativeGeometryCoordinate
  investigativeReceiptOnly
  "Authoritative Arcadis/Saunders Havill extent-of-work and vegetation-clearing vectors joined to authoritative Commonwealth 2014/7306 and 2019/8575 action/approval geometry. The existing raster receipt remains acquisition-routing evidence only."
  true true true false

imminencePayment : BlockingPayment
imminencePayment = blocking-payment
  imminenceCoordinate
  paymentOpen
  "Primary same-phase evidence of proposed or actual execution: pre-start record, Environmental Coordinator sign-off, fauna pre-clearance, contractor mobilisation, site notice or equivalent dated execution record."
  true true true false

standingCounselPayment : BlockingPayment
standingCounselPayment = blocking-payment
  standingCounselCoordinate
  paymentOpen
  "Counsel-grade standing, procedural-vehicle and statutory-exception analysis for any contemplated EPBC Act s 475 application or other restraint route."
  true false true false

currentBlockingPaymentState : List BlockingPayment
currentBlockingPaymentState =
  condition6aLiteralSubmissionPayment ∷
  samePhasePreclearancePayment ∷
  authoritativeGeometryPayment ∷
  imminencePayment ∷
  standingCounselPayment ∷
  []

------------------------------------------------------------------------
-- The live cut is intentionally fail-closed.  The source-derived spatial
-- receipt is useful enough to make Condition 6(a) extremely high-alpha, but
-- it cannot close the authoritative-geometry coordinate.
------------------------------------------------------------------------

record BlockingPromotionCut : Set where
  constructor blocking-promotion-cut
  field
    literalCondition6aPaid : Bool
    sameClearingPhasePaid : Bool
    authoritativeGeometryPaid : Bool
    imminencePaid : Bool
    counselStandingProcedurePaid : Bool
    eligibleForCounselExecutionEscalation : Bool
    legalContraventionEstablished : Bool

open BlockingPromotionCut public

condition6aAndSamePhaseRemainFirstCut : BlockingPromotionCut
condition6aAndSamePhaseRemainFirstCut = blocking-promotion-cut
  false false false false false false false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SourceDerivedGeometryPaysAuthoritativeGeometry : Set where
data Condition6aConditionTextPaysCondition6aSatisfaction : Set where
data SignedPreclearancePackagePaysFederalAuthorisation : Set where
data CounselEscalationEligibilityEqualsLegalConclusion : Set where

authoritativeGeometryBoundary : SourceDerivedGeometryPaysAuthoritativeGeometry → ⊥
authoritativeGeometryBoundary ()

sourceDerivedGeometryDoesNotPayAuthoritativeGeometry :
  SourceDerivedGeometryPaysAuthoritativeGeometry → ⊥
sourceDerivedGeometryDoesNotPayAuthoritativeGeometry ()

conditionTextDoesNotPayCondition6aSatisfaction :
  Condition6aConditionTextPaysCondition6aSatisfaction → ⊥
conditionTextDoesNotPayCondition6aSatisfaction ()

signedPreclearancePackageDoesNotPayFederalAuthorisation :
  SignedPreclearancePackagePaysFederalAuthorisation → ⊥
signedPreclearancePackageDoesNotPayFederalAuthorisation ()

counselEscalationEligibilityDoesNotEqualLegalConclusion :
  CounselEscalationEligibilityEqualsLegalConclusion → ⊥
counselEscalationEligibilityDoesNotEqualLegalConclusion ()

------------------------------------------------------------------------
-- Reuse only: no source or authority is re-minted in this owner.
------------------------------------------------------------------------

condition6aEvidenceReceipt : Evidence.Condition6aEvidenceObject
condition6aEvidenceReceipt = Evidence.condition6aLiteralSubmission

samePhasePackageReceipt : Evidence.Condition6aEvidenceObject
samePhasePackageReceipt = Evidence.signedEnvironmentalPreclearancePackage

sourceDerivedOverlapReceipt : P3.ApproximateOverlapReceipt
sourceDerivedOverlapReceipt = P3.approximateP3Receipt

section67AStatutoryGateReceipt : Cutset.CutsetEvidence
section67AStatutoryGateReceipt = Cutset.section67AControlledActionGate

section475RouteReceipt : Cutset.CutsetEvidence
section475RouteReceipt = Cutset.section475InjunctionRoute

record BlockingPaymentPareto : Set where
  constructor blocking-payment-pareto
  field
    literalCondition6aFirst : Bool
    samePhasePackageSecond : Bool
    authoritativeGeometryBeforeSameActionConclusion : Bool
    imminenceBeforeEmergencyReliefTheory : Bool
    counselReviewBeforeLegalConclusion : Bool
    sourceDerivedGeometryCanRouteAcquisition : Bool
    sourceDerivedGeometryCanPayAuthoritativeGeometry : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool
    conclusionMaySkipUnpaidDependency : Bool

canonicalBlockingPaymentPareto : BlockingPaymentPareto
canonicalBlockingPaymentPareto = blocking-payment-pareto
  true true true true true true false true false false
