module DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooPreservationSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- EPBC 2019/8575 CUMULATIVE-IMPACT SUFFICIENCY OWNER
------------------------------------------------------------------------

data EvidenceStatus : Set where
  primarySourcePaid : EvidenceStatus
  secondaryLocatorOnly : EvidenceStatus
  acquisitionOpen : EvidenceStatus
  consumerPaymentOpen : EvidenceStatus

data AnalysisComponent : Set where
  item46cRequirement : AnalysisComponent
  surroundingProjectsIdentity : AnalysisComponent
  sequentialFragmentationContext : AnalysisComponent
  localRegionalIntegration : AnalysisComponent
  finalPDSufficiency : AnalysisComponent

data ProjectCoordinate : Set where
  springviewVillageOne2014_7306 : ProjectCoordinate
  firstNineBrookwater2016_7676 : ProjectCoordinate
  woogarooHeights2017_7875 : ProjectCoordinate
  eugeneStreet2018_8350 : ProjectCoordinate
  peninsula2020_8629 : ProjectCoordinate
  scenic2020_8651 : ProjectCoordinate

projectCoordinateLabel : ProjectCoordinate → String
projectCoordinateLabel springviewVillageOne2014_7306 = "EPBC 2014/7306"
projectCoordinateLabel firstNineBrookwater2016_7676 = "EPBC 2016/7676"
projectCoordinateLabel woogarooHeights2017_7875 = "EPBC 2017/7875"
projectCoordinateLabel eugeneStreet2018_8350 = "EPBC 2018/8350"
projectCoordinateLabel peninsula2020_8629 = "EPBC 2020/8629"
projectCoordinateLabel scenic2020_8651 = "EPBC 2020/8651"

surroundingProjectCoordinates : List ProjectCoordinate
surroundingProjectCoordinates =
  springviewVillageOne2014_7306 ∷
  firstNineBrookwater2016_7676 ∷
  woogarooHeights2017_7875 ∷
  eugeneStreet2018_8350 ∷
  peninsula2020_8629 ∷
  scenic2020_8651 ∷
  []

record CumulativeImpactEvidence : Set where
  constructor cumulative-impact-evidence
  field
    component : AnalysisComponent
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : EvidenceStatus
    sourceIdentityImportsConclusion : Bool
    sourceIdentityImportsConclusionIsFalse : sourceIdentityImportsConclusion ≡ false

open CumulativeImpactEvidence public

localRegionalCumulativeAnalysisRequired : CumulativeImpactEvidence
localRegionalCumulativeAnalysisRequired = cumulative-impact-evidence
  item46cRequirement
  Atlas.springfield8575January2026PreliminaryDocumentation
  "Part A, section 4.2, Item 4.6(c) quotation"
  "The January 2026 PD quotes the Department request as requiring a local and regional scale analysis of likely impacts with reference to the project's potential contribution to cumulative impacts in the context of development patterns in the locality and region."
  primarySourcePaid
  false refl

surroundingProjectsKnown : CumulativeImpactEvidence
surroundingProjectsKnown = cumulative-impact-evidence
  surroundingProjectsIdentity
  Atlas.springfield8575January2026PreliminaryDocumentation
  "Plan A7 — Surrounding EPBC projects; koala/greater-glider context"
  "The January 2026 PD identifies surrounding and historical EPBC projects, including EPBC 2014/7306, EPBC 2016/7676, EPBC 2017/7875, EPBC 2018/8350, EPBC 2020/8629 and EPBC 2020/8651."
  primarySourcePaid
  false refl

sequentialFragmentationKnown : CumulativeImpactEvidence
sequentialFragmentationKnown = cumulative-impact-evidence
  sequentialFragmentationContext
  Atlas.springfield8575January2026PreliminaryDocumentation
  "Part A, greater-glider impact assessment / cumulative and sequential impacts"
  "The January 2026 PD attributes compromised landscape-level connectivity to cumulative and sequential development and historical habitat contraction."
  primarySourcePaid
  false refl

record CumulativeResponseResidual : Set where
  constructor cumulative-response-residual
  field
    requiredComponent : AnalysisComponent
    currentlyPaidByLocatedJanuaryPD : Bool
    exactMissingPayment : String
    laterPrimaryMaterialMayDischarge : Bool
    noInvalidityPromotion : Bool
    noInvalidityPromotionIsTrue : noInvalidityPromotion ≡ true

open CumulativeResponseResidual public

locatedLocalRegionalIntegrationResidual : CumulativeResponseResidual
locatedLocalRegionalIntegrationResidual = cumulative-response-residual
  localRegionalIntegration
  false
  "A same-object primary analysis quantitatively integrating the action's local/regional contribution with surrounding development patterns, habitat loss/retention, corridor function and cumulative risk has not yet been located in the January 2026 section 4.2 material inspected."
  true
  true refl

finalPDMayStillPayResidual : CumulativeResponseResidual
finalPDMayStillPayResidual = cumulative-response-residual
  finalPDSufficiency
  false
  "Acquire and inspect the post-comment Final PD, comment-response material, any cumulative-impact appendix, and any Department sufficiency review before promoting the apparent January response gap."
  true
  true refl

record SnowballPaymentBoundary : Set where
  constructor snowball-payment-boundary
  field
    outOfOrderAcquisitionAllowed : Bool
    primarySameObjectRequiredForPayment : Bool
    secondarySourcesMayLocatePrimaryObjects : Bool
    secondarySourcesMayPayPrimaryFacts : Bool
    projectIdentifierCreatesImpactEvidence : Bool
    finalConclusionMaySkipOpenDependencies : Bool

canonicalSnowballPaymentBoundary : SnowballPaymentBoundary
canonicalSnowballPaymentBoundary = snowball-payment-boundary
  true true true false false false

data SurroundingProjectMapPaysCumulativeAnalysis : Set where
data PastFragmentationDefinitionallyLowersMarginalValue : Set where
data MappedCorridorScorePaysFunctionalConnectivity : Set where
data RetentionEqualsAdditionalGain : Set where
data SecondarySourcePaysPrimaryFact : Set where
data ApparentResponseGapEqualsLegalInvalidity : Set where

surroundingProjectMapDoesNotPayCumulativeAnalysis :
  SurroundingProjectMapPaysCumulativeAnalysis → ⊥
surroundingProjectMapDoesNotPayCumulativeAnalysis ()

pastFragmentationDoesNotLowerMarginalValueByDefinition :
  PastFragmentationDefinitionallyLowersMarginalValue → ⊥
pastFragmentationDoesNotLowerMarginalValueByDefinition ()

mappedCorridorScoreDoesNotPayFunctionalConnectivity :
  MappedCorridorScorePaysFunctionalConnectivity → ⊥
mappedCorridorScoreDoesNotPayFunctionalConnectivity ()

retentionDoesNotEqualAdditionalGain : RetentionEqualsAdditionalGain → ⊥
retentionDoesNotEqualAdditionalGain ()

secondarySourceDoesNotPayPrimaryFact : SecondarySourcePaysPrimaryFact → ⊥
secondarySourceDoesNotPayPrimaryFact ()

apparentGapDoesNotEqualLegalInvalidity :
  ApparentResponseGapEqualsLegalInvalidity → ⊥
apparentGapDoesNotEqualLegalInvalidity ()

data CumulativeParetoLeaf : Set where
  finalPDAndCommentResponse : CumulativeParetoLeaf
  departmentSufficiencyReview : CumulativeParetoLeaf
  surroundingProjectPrimaryGeometry : CumulativeParetoLeaf
  timeIndexedHabitatLossLedger : CumulativeParetoLeaf
  speciesSpecificConnectivityComputation : CumulativeParetoLeaf

record CumulativeParetoPolicy : Set where
  constructor cumulative-pareto-policy
  field
    finalPDDoesFirstFalsification : Bool
    primaryProjectGeometryBeforeSecondaryAggregation : Bool
    shiftingBaselineKeptAsOpenAuditSeam : Bool
    sixOfSixCorridorScoreKeptDistinctFromFunction : Bool
    genericCumulativeDoctrineNeededBeforeItem46cAudit : Bool

canonicalCumulativeParetoPolicy : CumulativeParetoPolicy
canonicalCumulativeParetoPolicy = cumulative-pareto-policy true true true true false
