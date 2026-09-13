module DASHI.Reasoning.FibreRoutingRateDistortionInformationBottleneckSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as CompressionSnowball

------------------------------------------------------------------------
-- IBRAHIM CONTINUATION:
-- lossy compression <-> rate-distortion <-> relevance-preserving bottleneck
-- <-> consumer-relative projection adequacy.
--
-- Classical information-theoretic distortion/relevance criteria are external
-- mathematical/source coordinates.  DASHI's declared consumer remains the
-- authority for what must survive a particular formal projection.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim rate-distortion/information-bottleneck snowball"
  "verified external concept identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity checked 2026-09-11; QID does not select a distortion function, relevance variable, consumer, proof obligation or mechanism")

lossyCompressionQid : Identity.ExternalIdentityDemand
lossyCompressionQid = mkQid "lossy compression" "Q55564"

rateDistortionTheoryQid : Identity.ExternalIdentityDemand
rateDistortionTheoryQid = mkQid "rate-distortion theory" "Q843483"

representationQid : Identity.ExternalIdentityDemand
representationQid = mkQid "representation (generic)" "Q1272626"

informationBottleneckQid : Identity.ExternalIdentityDemand
informationBottleneckQid = Identity.mkOptionalIdentityDemand
  "Ibrahim rate-distortion/information-bottleneck snowball"
  "exact concept identity"
  "information bottleneck method"
  Identity.wikidataQid
  (Identity.unresolved
    "primary method source is available, but no exact same-concept QID is promoted in this pass; generic representation Q1272626 is not substituted")

sufficientStatisticQid : Identity.ExternalIdentityDemand
sufficientStatisticQid = Identity.mkOptionalIdentityDemand
  "Ibrahim rate-distortion/information-bottleneck snowball"
  "exact statistical concept identity"
  "sufficient statistic"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact QID promoted in this pass; statistical sufficiency remains conceptually distinct from DASHI consumer adequacy")

------------------------------------------------------------------------
-- Source role: primary and secondary/reference sources stay distinct.
------------------------------------------------------------------------

tishbyInformationBottleneckSource : Attribution.AttributedSource
tishbyInformationBottleneckSource = Attribution.mkNoDOISource
  "Naftali Tishby; Fernando C. Pereira; William Bialek"
  "The Information Bottleneck Method"
  "Proceedings of the 37th Annual Allerton Conference on Communication, Control, and Computing / arXiv:physics/0004057"
  "1999/2000"
  "https://arxiv.org/abs/physics/0004057"
  Attribution.academicArticleSource
  "primary information-bottleneck method source: seeks a short code retaining information relevant to another variable; does not define DASHI consumer adequacy or mechanistic realization"
  Attribution.publicAttribution

coverThomasRateDistortionSource : Attribution.AttributedSource
coverThomasRateDistortionSource = Attribution.mkDOISource
  "Thomas M. Cover; Joy A. Thomas"
  "Rate Distortion Theory"
  "Elements of Information Theory, Chapter 10"
  "2005"
  "10.1002/047174882X.ch10"
  "https://doi.org/10.1002/047174882X.ch10"
  Attribution.academicChapterSource
  "secondary/reference exposition of rate-distortion theory; source role is theorem/reference background, not historical priority claim"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- A distortion criterion is itself consumer-relative information.
------------------------------------------------------------------------

data DistortionCase : Set where
  sameRateConsumerSafe sameRateConsumerUnsafe : DistortionCase

data RateSurface : Set where sameCompressedRate : RateSurface
data ConsumerSafety : Set where consumerDecisionPreserved consumerDecisionChanged : ConsumerSafety

rateSurface : DistortionCase → RateSurface
rateSurface _ = sameCompressedRate

consumerSafety : DistortionCase → ConsumerSafety
consumerSafety sameRateConsumerSafe = consumerDecisionPreserved
consumerSafety sameRateConsumerUnsafe = consumerDecisionChanged

rateDoesNotDetermineConsumerSafety :
  consumerSafety sameRateConsumerSafe ≡ consumerSafety sameRateConsumerUnsafe → ⊥
rateDoesNotDetermineConsumerSafety ()

------------------------------------------------------------------------
-- Likewise, one scalar distortion value need not recover all consumer answers.
------------------------------------------------------------------------

data DistortionSurfaceCase : Set where
  sameDistortionRichRelationPreserved sameDistortionRichRelationLost : DistortionSurfaceCase

data DistortionSurface : Set where sameDeclaredDistortion : DistortionSurface
data RichRelationStatus : Set where richRelationRetained richRelationErased : RichRelationStatus

distortionSurface : DistortionSurfaceCase → DistortionSurface
distortionSurface _ = sameDeclaredDistortion

richRelationStatus : DistortionSurfaceCase → RichRelationStatus
richRelationStatus sameDistortionRichRelationPreserved = richRelationRetained
richRelationStatus sameDistortionRichRelationLost = richRelationErased

sameDistortionNeedNotPreserveEveryConsumer :
  richRelationStatus sameDistortionRichRelationPreserved ≡
  richRelationStatus sameDistortionRichRelationLost → ⊥
sameDistortionNeedNotPreserveEveryConsumer ()

------------------------------------------------------------------------
-- Exact reuse of the repo-native compression adequacy boundary.
------------------------------------------------------------------------

compressionBoundary : Ladder.FibreCompressionLadderBoundary
compressionBoundary = Ladder.canonicalFibreCompressionLadderBoundary

ibrahimCompressionBoundary : CompressionSnowball.FibreCompressionIbrahimSnowballBoundary
ibrahimCompressionBoundary = CompressionSnowball.canonicalFibreCompressionIbrahimSnowballBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record RateDistortionReverseConstraint : Set where
  constructor rate-distortion-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open RateDistortionReverseConstraint public

compressionConstraint : RateDistortionReverseConstraint
compressionConstraint = rate-distortion-reverse-constraint
  "Lossy compression / rate-distortion"
  "rate, distortion definition, source distribution, reconstruction carrier and declared downstream consumer remain separate"
  false

informationConstraint : RateDistortionReverseConstraint
informationConstraint = rate-distortion-reverse-constraint
  "Information bottleneck / relevance"
  "short code, relevance variable, retained information, prediction task and mechanism interpretation remain separate"
  false

representationConstraint : RateDistortionReverseConstraint
representationConstraint = rate-distortion-reverse-constraint
  "Representation / learning"
  "generic representational similarity does not determine sufficiency for every consumer; missing relation fibres may remain hidden"
  false

biologyConstraint : RateDistortionReverseConstraint
biologyConstraint = rate-distortion-reverse-constraint
  "Biological fibre compression"
  "compression metric cannot replace held-out structure/function adequacy or causal/mechanistic validation"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data LowDistortionMeansEveryConsumerSafe : Set where
data InformationBottleneckMeansMechanisticExplanation : Set where
data RateDistortionQidSelectsDistortion : Set where
data GenericRepresentationQidMeansRepresentationLearning : Set where
data StatisticalSufficiencyMeansEveryDashiConsumerAdequate : Set where

lowDistortionDoesNotMeanEveryConsumerSafe : LowDistortionMeansEveryConsumerSafe → ⊥
lowDistortionDoesNotMeanEveryConsumerSafe ()

informationBottleneckDoesNotMeanMechanisticExplanation : InformationBottleneckMeansMechanisticExplanation → ⊥
informationBottleneckDoesNotMeanMechanisticExplanation ()

rateDistortionQidDoesNotSelectDistortion : RateDistortionQidSelectsDistortion → ⊥
rateDistortionQidDoesNotSelectDistortion ()

genericRepresentationQidDoesNotMeanRepresentationLearning : GenericRepresentationQidMeansRepresentationLearning → ⊥
genericRepresentationQidDoesNotMeanRepresentationLearning ()

statisticalSufficiencyDoesNotMeanEveryConsumerAdequate : StatisticalSufficiencyMeansEveryDashiConsumerAdequate → ⊥
statisticalSufficiencyDoesNotMeanEveryDashiConsumerAdequate ()

record FibreRateDistortionInformationBottleneckBoundary : Set where
  constructor fibre-rate-distortion-information-bottleneck-boundary
  field
    safeQidsAttached : Bool
    unresolvedExactIdentitiesRetained : Bool
    primaryAndSecondarySourceRolesSeparated : Bool
    noDoiPrimarySourceRetainedCanonically : Bool
    distortionCriterionRemainsDeclared : Bool
    consumerAdequacyNotReplacedByScalarDistortion : Bool
    informationBottleneckNotMechanismClaim : Bool
    representationIdentityNotTaskSufficiency : Bool
    biologyStillNeedsHeldOutScientificConsumer : Bool
    presentAxisVocabularyClaimedComplete : Bool
open FibreRateDistortionInformationBottleneckBoundary public

canonicalFibreRateDistortionInformationBottleneckBoundary :
  FibreRateDistortionInformationBottleneckBoundary
canonicalFibreRateDistortionInformationBottleneckBoundary =
  fibre-rate-distortion-information-bottleneck-boundary
    true true true true true true true true true false
