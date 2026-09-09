module DASHI.Cognition.PNF.SensibLawGriffithsDirectionalSupportAuthorityRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Cognition.PNF.SensibLawGriffithsCustodialAuthorityCutV02Exact as AuthorityCut
import DASHI.Cognition.PNF.SensibLawGriffithsCustodialOutcomePaymentV02Exact as Outcome
import DASHI.Cognition.PNF.SensibLawCountryCommunityPaymentAcquisitionPlanV02Exact as Acquisition
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- GRIFFITHS SOURCE-SUPPORT / PRESENT-MANDATE REGRESSION
--
-- The narrow custodial outcome is already paid in the Country V02 lane.
-- This regression checks the opposite side of the new directional-source seam:
-- even an exact +1 source-support admission for that custodial proposition does
-- not alter the independently-open present-community-mandate residual.
------------------------------------------------------------------------

record PositiveGriffithsCustodialSourceSupport
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    (receipt : Verify.SourceVerificationReceipt demand)
    (admission : Verify.SourceSupportAdmission receipt) : Set₁ where
  constructor positiveGriffithsCustodialSourceSupport
  field
    sourceSupportPaidPositive : Verify.sourceSupportPaid admission ≡ true
    sourceSupportTritPositive : Verify.supportTrit admission ≡ Trit.pos
    sameNarrowCustodialProposition : Set
    sourceToCustodialPropositionWeld : Set
open PositiveGriffithsCustodialSourceSupport public

postPositiveSupportAuthorityResidual :
  ∀ {residual demand receipt admission} →
  PositiveGriffithsCustodialSourceSupport
    {residual} {demand} receipt admission →
  AuthorityCut.GriffithsAuthorityResidual
postPositiveSupportAuthorityResidual evidence =
  AuthorityCut.currentGriffithsAuthorityResidual

positiveSupportStillLeavesPresentMandateFirst :
  ∀ {residual demand receipt admission}
    (evidence : PositiveGriffithsCustodialSourceSupport
      {residual} {demand} receipt admission) →
  postPositiveSupportAuthorityResidual evidence
  ≡ AuthorityCut.presentCustodialMandateResidual
positiveSupportStillLeavesPresentMandateFirst evidence = refl

positiveSupportStillRoutesToAttributionProducer :
  Acquisition.producerForPaymentCoordinate AuthorityCut.nextSearchCoordinate
  ≡ Search.attributionProducer
positiveSupportStillRoutesToAttributionProducer = AuthorityCut.nextSearchProducerExact

narrowOutcomeRemainsPaid :
  Outcome.narrowConsumerOutcomePaid
    Outcome.canonicalGriffithsCustodialOutcomeBoundary ≡ true
narrowOutcomeRemainsPaid = refl

presentMandateRemainsUnpaid :
  AuthorityCut.presentMandatePaid
    AuthorityCut.canonicalGriffithsAuthorityCutBoundary ≡ false
presentMandateRemainsUnpaid = refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data PositiveCustodialSourceSupportCreatesPresentMandate : Set where
data PositiveCustodialSourceSupportCreatesAuthorityBearer : Set where
data PositiveCustodialSourceSupportRenewsHistoricalRepresentation : Set where
data PositiveCustodialSourceSupportPaysRoleScope : Set where

data PositiveCustodialSourceSupportPaysTemporalValidity : Set where

positiveSupportDoesNotCreatePresentMandate :
  PositiveCustodialSourceSupportCreatesPresentMandate → ⊥
positiveSupportDoesNotCreatePresentMandate ()

positiveSupportDoesNotCreateAuthorityBearer :
  PositiveCustodialSourceSupportCreatesAuthorityBearer → ⊥
positiveSupportDoesNotCreateAuthorityBearer ()

positiveSupportDoesNotRenewHistoricalRepresentation :
  PositiveCustodialSourceSupportRenewsHistoricalRepresentation → ⊥
positiveSupportDoesNotRenewHistoricalRepresentation ()

positiveSupportDoesNotPayRoleScope :
  PositiveCustodialSourceSupportPaysRoleScope → ⊥
positiveSupportDoesNotPayRoleScope ()

positiveSupportDoesNotPayTemporalValidity :
  PositiveCustodialSourceSupportPaysTemporalValidity → ⊥
positiveSupportDoesNotPayTemporalValidity ()

record GriffithsDirectionalSupportAuthorityBoundary : Set where
  constructor griffiths-directional-support-authority-boundary
  field
    narrowOutcomeAlreadyPaid : Bool
    positiveSourceSupportMayBeRepresented : Bool
    presentMandateStillFirstResidual : Bool
    nextProducerStillAttribution : Bool
    positiveSupportCreatesPresentMandate : Bool
    positiveSupportCreatesAuthorityBearer : Bool
    positiveSupportRenewsHistoricalRepresentation : Bool
    positiveSupportPaysRoleScope : Bool
    positiveSupportPaysTemporalValidity : Bool

canonicalGriffithsDirectionalSupportAuthorityBoundary :
  GriffithsDirectionalSupportAuthorityBoundary
canonicalGriffithsDirectionalSupportAuthorityBoundary =
  griffiths-directional-support-authority-boundary
    true true true true false false false false false
