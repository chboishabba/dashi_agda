module DASHI.Biology.IntersectionalFeedbackPrivacyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Intersectional and privacy governance for OEF feedback analysis.
--
-- Aggregate engagement is not equitable engagement.  Axis-aware analysis
-- may expose differential residuals only under consent, privacy,
-- minimum-cell, no-reidentification, and no-deficit-promotion gates.

data Never : Set where

data FeedbackAxis : Set where
  raceAxis : FeedbackAxis
  genderAxis : FeedbackAxis
  classAxis : FeedbackAxis
  disabilityAxis : FeedbackAxis
  neurotypeAxis : FeedbackAxis
  languageAxis : FeedbackAxis
  cultureAxis : FeedbackAxis
  caringRoleAxis : FeedbackAxis
  digitalAccessAxis : FeedbackAxis
  priorEducationAxis : FeedbackAxis
  institutionalTrustAxis : FeedbackAxis

canonicalFeedbackAxes : List FeedbackAxis
canonicalFeedbackAxes =
  raceAxis
  ∷ genderAxis
  ∷ classAxis
  ∷ disabilityAxis
  ∷ neurotypeAxis
  ∷ languageAxis
  ∷ cultureAxis
  ∷ caringRoleAxis
  ∷ digitalAccessAxis
  ∷ priorEducationAxis
  ∷ institutionalTrustAxis
  ∷ []

record AxisBundle : Set where
  constructor mkAxisBundle
  field
    bundleLabel : String
    bundleAxes : List FeedbackAxis
    bundleIntersectionPreserved : Bool
    bundleIntersectionPreservedIsTrue : bundleIntersectionPreserved ≡ true
    bundleNoSingleAxisReduction : Bool
    bundleNoSingleAxisReductionIsTrue : bundleNoSingleAxisReduction ≡ true

open AxisBundle public

canonicalIntersectionalFeedbackAxisBundle : AxisBundle
canonicalIntersectionalFeedbackAxisBundle =
  mkAxisBundle
    "intersectional student-feedback axis bundle"
    canonicalFeedbackAxes
    true refl
    true refl

record PrivacyGate : Set where
  constructor mkPrivacyGate
  field
    gateLabel : String
    optInConsentRequired : Bool
    optInConsentRequiredIsTrue : optInConsentRequired ≡ true
    privacyRequired : Bool
    privacyRequiredIsTrue : privacyRequired ≡ true
    minimumCellSizeRequired : Bool
    minimumCellSizeRequiredIsTrue : minimumCellSizeRequired ≡ true
    noReidentificationRequired : Bool
    noReidentificationRequiredIsTrue : noReidentificationRequired ≡ true
    noDeficitPromotionRequired : Bool
    noDeficitPromotionRequiredIsTrue : noDeficitPromotionRequired ≡ true
    localContextReviewRequired : Bool
    localContextReviewRequiredIsTrue : localContextReviewRequired ≡ true

open PrivacyGate public

canonicalFeedbackPrivacyGate : PrivacyGate
canonicalFeedbackPrivacyGate =
  mkPrivacyGate
    "intersectional feedback privacy gate"
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record AxisAwarePrediction : Set where
  constructor mkAxisAwarePrediction
  field
    predictionLabel : String
    predictionCourseSurface : String
    predictionTimeSurface : String
    predictionElement : OEF.OEFElement
    predictionAxisBundle : AxisBundle
    predictionAvailableCount : Nat
    predictionPrivacyGate : PrivacyGate
    predictionAggregateOnly : Bool
    predictionAggregateOnlyIsTrue : predictionAggregateOnly ≡ true
    predictionNotIndividualDiagnosis : Bool
    predictionNotIndividualDiagnosisIsTrue : predictionNotIndividualDiagnosis ≡ true
    predictionNotDeficitEvidence : Bool
    predictionNotDeficitEvidenceIsTrue : predictionNotDeficitEvidence ≡ true
    predictionNotEquityClosure : Bool
    predictionNotEquityClosureIsTrue : predictionNotEquityClosure ≡ true

open AxisAwarePrediction public

canonicalAxisAwarePrediction : AxisAwarePrediction
canonicalAxisAwarePrediction =
  mkAxisAwarePrediction
    "axis-aware emotional engagement aggregate candidate"
    "course or programme surface"
    "semester surface"
    OEF.emotionalEngagement
    canonicalIntersectionalFeedbackAxisBundle
    0
    canonicalFeedbackPrivacyGate
    true refl
    true refl
    true refl
    true refl

data PrivacyPromotionRoute : Set where
  governedAggregateRoute : PrivacyPromotionRoute
  axisErasureRoute : PrivacyPromotionRoute
  smallCellDisclosureRoute : PrivacyPromotionRoute
  reidentificationRoute : PrivacyPromotionRoute
  demographicDeficitRoute : PrivacyPromotionRoute
  aggregateEqualsEquityRoute : PrivacyPromotionRoute

AdmissiblePrivacyPromotionRoute : PrivacyPromotionRoute → Set
AdmissiblePrivacyPromotionRoute governedAggregateRoute = ⊤
AdmissiblePrivacyPromotionRoute axisErasureRoute = Never
AdmissiblePrivacyPromotionRoute smallCellDisclosureRoute = Never
AdmissiblePrivacyPromotionRoute reidentificationRoute = Never
AdmissiblePrivacyPromotionRoute demographicDeficitRoute = Never
AdmissiblePrivacyPromotionRoute aggregateEqualsEquityRoute = Never

governedAggregateRouteAdmissible :
  AdmissiblePrivacyPromotionRoute governedAggregateRoute
governedAggregateRouteAdmissible = tt

axisErasureBlocked :
  AdmissiblePrivacyPromotionRoute axisErasureRoute → Never
axisErasureBlocked ()

smallCellDisclosureBlocked :
  AdmissiblePrivacyPromotionRoute smallCellDisclosureRoute → Never
smallCellDisclosureBlocked ()

reidentificationBlocked :
  AdmissiblePrivacyPromotionRoute reidentificationRoute → Never
reidentificationBlocked ()

demographicDeficitBlocked :
  AdmissiblePrivacyPromotionRoute demographicDeficitRoute → Never
demographicDeficitBlocked ()

aggregateEqualsEquityBlocked :
  AdmissiblePrivacyPromotionRoute aggregateEqualsEquityRoute → Never
aggregateEqualsEquityBlocked ()

record IntersectionalFeedbackPrivacyBoundary : Set where
  constructor mkIntersectionalFeedbackPrivacyBoundary
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    axisBundle : AxisBundle
    axisBundleIsCanonical : axisBundle ≡ canonicalIntersectionalFeedbackAxisBundle
    privacyGate : PrivacyGate
    privacyGateIsCanonical : privacyGate ≡ canonicalFeedbackPrivacyGate
    axisAwarePrediction : AxisAwarePrediction
    axisAwarePredictionIsCanonical : axisAwarePrediction ≡ canonicalAxisAwarePrediction
    route : PrivacyPromotionRoute
    routeIsGoverned : route ≡ governedAggregateRoute
    routeAdmissible : AdmissiblePrivacyPromotionRoute route
    intersectionalAxesNotErased : Bool
    intersectionalAxesNotErasedIsTrue : intersectionalAxesNotErased ≡ true
    aggregateEngagementNotEquity : Bool
    aggregateEngagementNotEquityIsTrue : aggregateEngagementNotEquity ≡ true
    noReidentification : Bool
    noReidentificationIsTrue : noReidentification ≡ true
    noDeficitPromotion : Bool
    noDeficitPromotionIsTrue : noDeficitPromotion ≡ true
    reading : String

open IntersectionalFeedbackPrivacyBoundary public

canonicalIntersectionalFeedbackPrivacyBoundary :
  IntersectionalFeedbackPrivacyBoundary
canonicalIntersectionalFeedbackPrivacyBoundary =
  mkIntersectionalFeedbackPrivacyBoundary
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalIntersectionalFeedbackAxisBundle refl
    canonicalFeedbackPrivacyGate refl
    canonicalAxisAwarePrediction refl
    governedAggregateRoute refl tt
    true refl
    true refl
    true refl
    true refl
    "OEF aggregate signals may be stratified by available opt-in axes only under privacy and minimum-cell governance. High average engagement does not establish equitable engagement, and group differences do not promote individual diagnosis or deficit ontology."

AggregateEngagementNotEquity : Set
AggregateEngagementNotEquity =
  aggregateEngagementNotEquity canonicalIntersectionalFeedbackPrivacyBoundary ≡ true

aggregateEngagementNotEquityProof : AggregateEngagementNotEquity
aggregateEngagementNotEquityProof =
  aggregateEngagementNotEquityIsTrue canonicalIntersectionalFeedbackPrivacyBoundary
