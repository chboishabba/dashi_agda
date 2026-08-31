module DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact where

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionSupportDemandFarCrossPollinationExact as Far
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionConsumerObservationDemandPreorderExact as Demand
import DASHI.Culture.IntellectualReceptionIntersectionalInformationGeometryExact as IntersectionalInfo

------------------------------------------------------------------------
-- 1. A small proof-relevant two-level order for each declared information axis.
-- strong means preferable only relative to that axis' declared objective.
------------------------------------------------------------------------

data AxisLevel : Set where
  weak strong : AxisLevel

data AtMostAxis : AxisLevel → AxisLevel → Set where
  weak-weak : AtMostAxis weak weak
  weak-strong : AtMostAxis weak strong
  strong-strong : AtMostAxis strong strong

axisRefl : (x : AxisLevel) → AtMostAxis x x
axisRefl weak = weak-weak
axisRefl strong = strong-strong

axisTrans :
  ∀ {a b c} →
  AtMostAxis a b →
  AtMostAxis b c →
  AtMostAxis a c
axisTrans weak-weak bc = bc
axisTrans weak-strong strong-strong = weak-strong
axisTrans strong-strong strong-strong = strong-strong

strongNotAtMostWeak : AtMostAxis strong weak → ⊥
strongNotAtMostWeak ()

------------------------------------------------------------------------
-- 2. Situated information profile.
--
-- Axes remain semantically distinct. In particular, observation demand uses
-- "strong" for easier/current-filtration separation, while provenance and
-- authority use "strong" for the stronger declared lineage/standing receipt.
------------------------------------------------------------------------

record SituatedInformationProfile : Set where
  constructor situated-information-profile
  field
    supportRichness : AxisLevel
    separationAccessibility : AxisLevel
    measurementEconomy : AxisLevel
    residualDecoupling : AxisLevel
    provenanceStrength : AxisLevel
    authorityStrength : AxisLevel

open SituatedInformationProfile public

------------------------------------------------------------------------
-- 3. Product/Pareto preorder: componentwise no-worse on every declared axis.
------------------------------------------------------------------------

record ParetoNoWorse
    (left right : SituatedInformationProfile) : Set where
  constructor pareto-no-worse
  field
    supportOrder : AtMostAxis (supportRichness left) (supportRichness right)
    separationOrder :
      AtMostAxis (separationAccessibility left) (separationAccessibility right)
    measurementOrder :
      AtMostAxis (measurementEconomy left) (measurementEconomy right)
    residualOrder :
      AtMostAxis (residualDecoupling left) (residualDecoupling right)
    provenanceOrder :
      AtMostAxis (provenanceStrength left) (provenanceStrength right)
    authorityOrder :
      AtMostAxis (authorityStrength left) (authorityStrength right)

open ParetoNoWorse public

paretoRefl : (profile : SituatedInformationProfile) → ParetoNoWorse profile profile
paretoRefl profile =
  pareto-no-worse
    (axisRefl (supportRichness profile))
    (axisRefl (separationAccessibility profile))
    (axisRefl (measurementEconomy profile))
    (axisRefl (residualDecoupling profile))
    (axisRefl (provenanceStrength profile))
    (axisRefl (authorityStrength profile))

paretoTrans :
  ∀ {a b c} →
  ParetoNoWorse a b →
  ParetoNoWorse b c →
  ParetoNoWorse a c
paretoTrans ab bc =
  pareto-no-worse
    (axisTrans (supportOrder ab) (supportOrder bc))
    (axisTrans (separationOrder ab) (separationOrder bc))
    (axisTrans (measurementOrder ab) (measurementOrder bc))
    (axisTrans (residualOrder ab) (residualOrder bc))
    (axisTrans (provenanceOrder ab) (provenanceOrder bc))
    (axisTrans (authorityOrder ab) (authorityOrder bc))

------------------------------------------------------------------------
-- 4. Canonical crossed profiles.
--
-- discriminatorProfile is richer/easier/cheaper/better-decoupled on the
-- observation side but only introduced/weak on provenance and authority.
-- governedProfile has weaker observational convenience but stronger inherited
-- provenance and authority. Neither dominates the other.
------------------------------------------------------------------------

discriminatorProfile : SituatedInformationProfile
discriminatorProfile =
  situated-information-profile
    strong
    strong
    strong
    strong
    weak
    weak

governedProfile : SituatedInformationProfile
governedProfile =
  situated-information-profile
    weak
    weak
    weak
    weak
    strong
    strong

discriminatorNotParetoBelowGoverned :
  ParetoNoWorse discriminatorProfile governedProfile → ⊥
discriminatorNotParetoBelowGoverned witness =
  strongNotAtMostWeak (supportOrder witness)

governedNotParetoBelowDiscriminator :
  ParetoNoWorse governedProfile discriminatorProfile → ⊥
governedNotParetoBelowDiscriminator witness =
  strongNotAtMostWeak (provenanceOrder witness)

record ParetoIncomparable
    (left right : SituatedInformationProfile) : Set where
  constructor pareto-incomparable
  field
    leftNotBelowRight : ParetoNoWorse left right → ⊥
    rightNotBelowLeft : ParetoNoWorse right left → ⊥

open ParetoIncomparable public

canonicalSituatedInformationIncomparability :
  ParetoIncomparable discriminatorProfile governedProfile
canonicalSituatedInformationIncomparability =
  pareto-incomparable
    discriminatorNotParetoBelowGoverned
    governedNotParetoBelowDiscriminator

------------------------------------------------------------------------
-- 5. Same-repo receipts grounding the crossed interpretation.
------------------------------------------------------------------------

supportActuallyGrows :
  Far.StrictSupportIncluded
    Reuse.presentFutureSupport
    Reuse.authoritySensitiveSupport
supportActuallyGrows = Far.presentFutureStrictlyIncludedInAuthority

authoritySupportActuallyEasierToSeparate :
  Demand.ConsumerNoMoreObservationDemanding
    Reuse.authoritySensitiveSupport
    Reuse.presentFutureSupport
authoritySupportActuallyEasierToSeparate =
  Demand.authorityNoMoreDemandingThanPresentFuture

intersectionalSingleAxesStillInsufficient :
  IntersectionalInfo.IntellectualReceptionIntersectionalInformationGeometryBoundary
intersectionalSingleAxesStillInsufficient =
  IntersectionalInfo.canonicalIntellectualReceptionIntersectionalInformationGeometryBoundary

------------------------------------------------------------------------
-- 6. No scalarization / no value-ranking promotion.
------------------------------------------------------------------------

data ParetoOrderPromotesSingleScalarQuality : Set where
data ParetoOrderPromotesTruthRanking : Set where
data ParetoOrderPromotesMoralRanking : Set where
data ParetoIncomparabilityPromotesEqualImportance : Set where
data StrongAxisMeansUniversallyBetter : Set where

paretoDoesNotPromoteSingleScalarQuality :
  ParetoOrderPromotesSingleScalarQuality → ⊥
paretoDoesNotPromoteSingleScalarQuality ()

paretoDoesNotPromoteTruthRanking : ParetoOrderPromotesTruthRanking → ⊥
paretoDoesNotPromoteTruthRanking ()

paretoDoesNotPromoteMoralRanking : ParetoOrderPromotesMoralRanking → ⊥
paretoDoesNotPromoteMoralRanking ()

incomparabilityDoesNotPromoteEqualImportance :
  ParetoIncomparabilityPromotesEqualImportance → ⊥
incomparabilityDoesNotPromoteEqualImportance ()

axisStrengthIsObjectiveRelative : StrongAxisMeansUniversallyBetter → ⊥
axisStrengthIsObjectiveRelative ()

record IntellectualReceptionSituatedInformationParetoBoundary : Set where
  constructor intellectual-reception-situated-information-pareto-boundary
  field
    productOrderIsReflexive : Bool
    productOrderIsTransitive : Bool
    explicitIncomparableProfilesConstructed : Bool
    richerSupportCanTradeAgainstProvenance : Bool
    easierSeparationCanTradeAgainstAuthority : Bool
    paretoOrderIsSingleScalarQuality : Bool
    paretoOrderRanksTruth : Bool
    paretoOrderRanksMoralWorth : Bool
    intersectionalSingleAxisBoundaryRetained : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionSituatedInformationParetoBoundary :
  IntellectualReceptionSituatedInformationParetoBoundary
canonicalIntellectualReceptionSituatedInformationParetoBoundary =
  intellectual-reception-situated-information-pareto-boundary
    true true true true true false false false true true
