module DASHI.Cognition.PNF.SensibLawGriffithsCustodialAuthorityIntrospectionV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGriffithsCustodialAuthorityCutV02Exact as Cut
import DASHI.Cognition.PNF.SensibLawCountryCommunityPaymentAcquisitionPlanV02Exact as Acquisition
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- INTROSPECTIVE BINDING FOR THE LIVE GRIFFITHS AUTHORITY RESIDUAL
--
-- The narrow custodial outcome is already paid.  The next live defect is the
-- present mandate for that same consumer.  A source/search route counts as
-- progress only when it is bound to this exact residual, coordinate and
-- producer; historical litigation representation or generic community-role
-- evidence cannot silently substitute for the missing present mandate.
------------------------------------------------------------------------

record BoundPresentMandateDemandV02 : Set where
  constructor bound-present-mandate-demand-v02
  field
    liveResidual : Cut.GriffithsAuthorityResidual
    liveResidualIsCurrent : liveResidual ≡ Cut.currentGriffithsAuthorityResidual
    paymentCoordinate : Acquisition.PaymentCoordinate
    coordinateIsCurrent : paymentCoordinate ≡ Cut.nextSearchCoordinate
    producer : Search.ProducerClass
    producerIsCurrent : producer ≡ Acquisition.producerForPaymentCoordinate paymentCoordinate
    exactConsumerPreserved : Set
    presentTemporalEnvelopePreserved : Set
    mandateScopePreserved : Set
    sourceRoutePaysPresentMandate : Bool
    sourceRoutePaysPresentMandateIsFalse : sourceRoutePaysPresentMandate ≡ false

open BoundPresentMandateDemandV02 public

currentBoundPresentMandateDemandV02 : BoundPresentMandateDemandV02
currentBoundPresentMandateDemandV02 =
  bound-present-mandate-demand-v02
    Cut.currentGriffithsAuthorityResidual
    refl
    Cut.nextSearchCoordinate
    refl
    Search.attributionProducer
    refl
    Set
    Set
    Set
    false
    refl

currentBoundResidualIsPresentMandate :
  liveResidual currentBoundPresentMandateDemandV02 ≡ Cut.presentCustodialMandateResidual
currentBoundResidualIsPresentMandate = refl

currentBoundCoordinateIsMandateScope :
  paymentCoordinate currentBoundPresentMandateDemandV02 ≡ Acquisition.communityMandateScopeCoordinate
currentBoundCoordinateIsMandateScope = refl

currentBoundProducerIsAttribution :
  producer currentBoundPresentMandateDemandV02 ≡ Search.attributionProducer
currentBoundProducerIsAttribution = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BoundSearchPaysMandate : Set where
data HistoricalRolePaysPresentMandate : Set where
data StateStatisticPaysCommunityMandate : Set where
data VisualizationPaysMandate : Set where

boundSearchDoesNotPayMandate : BoundSearchPaysMandate → ⊥
boundSearchDoesNotPayMandate ()

historicalRoleDoesNotPayPresentMandate : HistoricalRolePaysPresentMandate → ⊥
historicalRoleDoesNotPayPresentMandate ()

stateStatisticDoesNotPayCommunityMandate : StateStatisticPaysCommunityMandate → ⊥
stateStatisticDoesNotPayCommunityMandate ()

visualizationDoesNotPayMandate : VisualizationPaysMandate → ⊥
visualizationDoesNotPayMandate ()
