module DASHI.Governance.ReligiousChildhoodInstantiationEvidenceAtlasExact where

------------------------------------------------------------------------
-- RELIGIOUS-CHILDHOOD DOMAIN-INSTANTIATION EVIDENCE ATLAS
--
-- This closes part of the empirical hole left explicit by
-- JohnPaperClaimManifestV2Exact.  Each source inhabits only the coordinates its
-- design actually measures.  No row alone establishes entrapment, trauma,
-- causation, or a population-wide religious-harm claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.ChildReligiousCoercionResearchBridge as Research

------------------------------------------------------------------------
-- Coordinates named in the John-paper dependency graph.
------------------------------------------------------------------------

data ReligiousChildhoodCoordinate : Set where
  divinePunishmentFear
  familyReligiousTransmission
  autonomySupportOrControl
  apostasyOrExitTransition
  refusalPenalty
  restrictedAlternatives
  developmentalTiming
  : ReligiousChildhoodCoordinate

data CoverageStatus : Set where
  directMeasuredCoverage
  partialProxyCoverage
  contextualCoverage
  notCovered
  : CoverageStatus

data StudyDesignClass : Set where
  parentChildDiaryStudy
  retrospectiveCollegeSample
  surveyAssociationStudy
  scaleValidationStudy
  religiousSocializationStudy
  : StudyDesignClass

record EmpiricalSourceReceipt : Set where
  constructor empirical-source-receipt
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    designClass : StudyDesignClass
    boundedRole : String

open EmpiricalSourceReceipt public

boyatzisJanicki : EmpiricalSourceReceipt
boyatzisJanicki = empirical-source-receipt
  "Chris J. Boyatzis; Denise L. Janicki"
  "Parent-Child Communication about Religion: Survey and Diary Data on Unilateral Transmission and Bi-Directional Reciprocity Styles"
  "Review of Religious Research 44(3), 252-270"
  2003
  "DOI 10.2307/3512386"
  parentChildDiaryStudy
  "measures parent-child religious communication and reciprocal versus unilateral styles in Christian families with children; does not measure coercive harm or entrapment"

hunsbergerBrown : EmpiricalSourceReceipt
hunsbergerBrown = empirical-source-receipt
  "Bruce Hunsberger; L. B. Brown"
  "Religious Socialization, Apostasy, and the Impact of Family Background"
  "Journal for the Scientific Study of Religion 23(3), 239-251"
  1984
  "DOI 10.2307/1386039"
  religiousSocializationStudy
  "supports study of family-background religious socialization and apostasy/disaffiliation relations; does not establish coercive exit penalties in a child sample"

williamsEtAl : EmpiricalSourceReceipt
williamsEtAl = empirical-source-receipt
  "Paul D. Williams; William M. Hunter; Elizabeth Seyer; Stephen Sammut; Matthew M. Breuninger"
  "Religious/spiritual struggles and perceived parenting style in a religious college-aged sample"
  "Mental Health, Religion & Culture 22(5), 500-516"
  2019
  "DOI 10.1080/13674676.2019.1629402"
  retrospectiveCollegeSample
  "Catholic college sample; perceived parental warmth/involvement/autonomy support related to religious-spiritual struggle, and fear-of-God-punishment scrupulosity independently predicted moral struggle; retrospective association, not childhood causal identification"

exlineEtAl : EmpiricalSourceReceipt
exlineEtAl = empirical-source-receipt
  "Julie J. Exline; Kenneth I. Pargament; Joshua B. Grubbs; Ann Marie Yali"
  "The Religious and Spiritual Struggles Scale: Development and initial validation"
  "Psychology of Religion and Spirituality 6(3), 208-222"
  2014
  "DOI 10.1037/a0036465"
  scaleValidationStudy
  "validates measurement domains including divine, demonic, interpersonal, moral, doubt and ultimate-meaning struggle; measurement receipt, not developmental etiology"

------------------------------------------------------------------------
-- Source x coordinate coverage.  This is deliberately sparse.
------------------------------------------------------------------------

coverage : EmpiricalSourceReceipt → ReligiousChildhoodCoordinate → CoverageStatus
coverage s divinePunishmentFear with identifier s
... | "DOI 10.1080/13674676.2019.1629402" = directMeasuredCoverage
... | "DOI 10.1037/a0036465" = contextualCoverage
... | _ = notCovered
coverage s familyReligiousTransmission with identifier s
... | "DOI 10.2307/3512386" = directMeasuredCoverage
... | "DOI 10.2307/1386039" = directMeasuredCoverage
... | _ = notCovered
coverage s autonomySupportOrControl with identifier s
... | "DOI 10.1080/13674676.2019.1629402" = directMeasuredCoverage
... | "DOI 10.2307/3512386" = partialProxyCoverage
... | _ = notCovered
coverage s apostasyOrExitTransition with identifier s
... | "DOI 10.2307/1386039" = directMeasuredCoverage
... | _ = notCovered
coverage _ refusalPenalty = notCovered
coverage _ restrictedAlternatives = notCovered
coverage s developmentalTiming with identifier s
... | "DOI 10.2307/3512386" = directMeasuredCoverage
... | "DOI 10.2307/1386039" = contextualCoverage
... | _ = notCovered

------------------------------------------------------------------------
-- The atlas therefore narrows the missing receipt rather than declaring it
-- solved.  Hell/divine-punishment fear, transmission, autonomy support,
-- apostasy, and developmental timing have some empirical occupancy; explicit
-- refusal penalty and restricted-alternative coordinates remain unfilled here.
------------------------------------------------------------------------

record ReligiousChildhoodInstantiationReceipt : Set where
  constructor religious-childhood-instantiation-receipt
  field
    divinePunishmentEvidence : EmpiricalSourceReceipt
    transmissionEvidence : EmpiricalSourceReceipt
    autonomyEvidence : EmpiricalSourceReceipt
    apostasyEvidence : EmpiricalSourceReceipt
    developmentalEvidence : EmpiricalSourceReceipt
    refusalPenaltyStillMissing : Bool
    restrictedAlternativesStillMissing : Bool
    causalEntrapmentEstablished : Bool
    ordinaryReligionPromotedToHarm : Bool

canonicalReligiousChildhoodInstantiationReceipt :
  ReligiousChildhoodInstantiationReceipt
canonicalReligiousChildhoodInstantiationReceipt =
  religious-childhood-instantiation-receipt
    williamsEtAl
    boyatzisJanicki
    williamsEtAl
    hunsbergerBrown
    boyatzisJanicki
    true true false false

------------------------------------------------------------------------
-- Crosswalk into the existing dimensional research bridge.
------------------------------------------------------------------------

fearDimension : Research.ExposureDimension
fearDimension = Research.fearExposure

punishmentDimension : Research.ExposureDimension
punishmentDimension = Research.punishmentExposure

epistemicClosureDimension : Research.ExposureDimension
epistemicClosureDimension = Research.epistemicClosureExposure

record AtlasPromotionBoundary : Set where
  constructor atlas-promotion-boundary
  field
    divinePunishmentAssociationEqualsEntrapment : Bool
    apostasyStudyProvesExitPenalty : Bool
    religiousCommunicationEqualsCoercion : Bool
    scaleValidationProvesChildhoodEtiology : Bool
    currentAtlasClosesRefusalPenaltyPremise : Bool
    currentAtlasClosesRestrictedAlternativesPremise : Bool
    atlasProvidesPartialDomainInstantiation : Bool

canonicalAtlasPromotionBoundary : AtlasPromotionBoundary
canonicalAtlasPromotionBoundary =
  atlas-promotion-boundary false false false false false false true
