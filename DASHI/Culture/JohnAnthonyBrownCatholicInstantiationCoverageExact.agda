module DASHI.Culture.JohnAnthonyBrownCatholicInstantiationCoverageExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: CATHOLIC INSTANTIATION COVERAGE
--
-- Authorial programme source: John Anthony Brown.
--
-- This owner cross-pollinates the religious-childhood evidence work without
-- importing an unmerged sibling branch.  Its purpose is to replace the coarse
-- statement "Catholic evidence missing" with coordinate-wise coverage.
--
-- Source attribution rule:
-- source proposition != John Anthony Brown proposition != DASHI theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record StudySource : Set where
  constructor study-source
  field
    authors : String
    title : String
    year : String
    venue : String
    doi : String
    population : String
    sourceRole : String

open StudySource public

williamsEtAl2019 : StudySource
williamsEtAl2019 = study-source
  "Paul D. Williams; William M. Hunter; Elizabeth Seyer; Stephen Sammut; Matthew M. Breuninger"
  "Religious/spiritual struggles and perceived parenting style in a religious college-aged sample"
  "2019"
  "Mental Health, Religion & Culture 22(5):500-516"
  "10.1080/13674676.2019.1629402"
  "Catholic college students, n = 464"
  "retrospective Catholic-sample association source for perceived parenting/autonomy support, religious-spiritual struggle, scrupulosity, and fear of God's punishment; not a coercion, PTSD, prevalence, or longitudinal childhood-effect study"

boyatzisJanicki2003 : StudySource
boyatzisJanicki2003 = study-source
  "Chris J. Boyatzis; Denise L. Janicki"
  "Parent-Child Communication about Religion: Survey and Diary Data on Unilateral Transmission and Bi-Directional Reciprocity Styles"
  "2003"
  "Review of Religious Research 44(3):252-270"
  "10.2307/3512386"
  "Christian parents with children aged 3-12 years; Time 1 n = 23 families, Time 2 n = 15"
  "direct developmental/family religious-communication source; shows children can be active participants in religious socialisation; does not measure coercion, trauma, refusal penalty, or Catholic-specific effects"

hunsbergerBrown1984 : StudySource
hunsbergerBrown1984 = study-source
  "Bruce Hunsberger; L. B. Brown"
  "Religious Socialization, Apostasy, and the Impact of Family Background"
  "1984"
  "Journal for the Scientific Study of Religion 23(3):239-251"
  "10.2307/1386039"
  "family-background / religious-socialisation and apostasy study"
  "exit/apostasy and family-socialisation source; does not by itself establish coercive exit cost, refusal punishment, or Catholic-specific clinical harm"

nakamuraEtAl2026 : StudySource
nakamuraEtAl2026 = study-source
  "Julia S. Nakamura; J. P. De Gance; Isaiah Contu; Katheryn C. H. Yang; Rachel S. Leong; Richard G. Cowden; Katelyn N. G. Long; Tyler J. VanderWeele"
  "Associations of Childhood Experiences With Adulthood Religious and Relational Outcomes Among Protestants and Catholics in the United States"
  "2026"
  "Journal for the Scientific Study of Religion 65(2):386-398"
  "10.1111/jssr.70039"
  "16,548 adult congregants from 32 Protestant and Catholic congregations in the United States"
  "large retrospective childhood-experience/adult religious-relational outcome source; establishes temporal-domain adjacency and relational transmission patterns but does not measure coercive exposure, trauma/PTSS, refusal penalty, or Catholic-only effects"

------------------------------------------------------------------------
-- Coordinate-wise coverage rather than one Boolean 'Catholic evidence'.
------------------------------------------------------------------------

data CatholicTargetCoordinate : Set where
  divinePunishmentFear : CatholicTargetCoordinate
  parentAutonomySupportOrControl : CatholicTargetCoordinate
  familyReligiousTransmission : CatholicTargetCoordinate
  apostasyExitTransition : CatholicTargetCoordinate
  refusalPenalty : CatholicTargetCoordinate
  restrictedAlternatives : CatholicTargetCoordinate
  developmentalTiming : CatholicTargetCoordinate
  adultClinicalDistressPTSS : CatholicTargetCoordinate
  adjustedClinicalAssociation : CatholicTargetCoordinate
  prospectiveTemporalIdentification : CatholicTargetCoordinate

data CoverageStatus : Set where
  directMeasured : CoverageStatus
  retrospectiveProxy : CoverageStatus
  contextualSupport : CoverageStatus
  missing : CoverageStatus

record CoverageReceipt : Set where
  constructor coverage-receipt
  field
    coordinate : CatholicTargetCoordinate
    status : CoverageStatus
    source : StudySource
    boundedReading : String

open CoverageReceipt public

catholicPunishmentFearCoverage : CoverageReceipt
catholicPunishmentFearCoverage = coverage-receipt
  divinePunishmentFear directMeasured williamsEtAl2019
  "fear-of-God's-punishment scrupulosity was measured in a Catholic college sample and independently predicted greater Moral religious/spiritual struggle; this is not a childhood coercion or trauma effect"

catholicAutonomySupportCoverage : CoverageReceipt
catholicAutonomySupportCoverage = coverage-receipt
  parentAutonomySupportOrControl retrospectiveProxy williamsEtAl2019
  "perceived parental warmth, involvement, and autonomy support were associated with lower overall religious/spiritual struggle; parenting is recalled and the outcome is struggle, not a direct autonomy-loss endpoint"

familyTransmissionCoverage : CoverageReceipt
familyTransmissionCoverage = coverage-receipt
  familyReligiousTransmission directMeasured boyatzisJanicki2003
  "religious communication was observed/reported in families with children aged 3-12 and often showed bidirectional reciprocity rather than passive one-way transmission"

apostasyCoverage : CoverageReceipt
apostasyCoverage = coverage-receipt
  apostasyExitTransition contextualSupport hunsbergerBrown1984
  "family religious background and apostasy are empirically connected research objects; explicit refusal penalty and constrained exit remain separate missing coordinates"

developmentalTimingCoverage : CoverageReceipt
developmentalTimingCoverage = coverage-receipt
  developmentalTiming directMeasured boyatzisJanicki2003
  "religious socialisation is directly observed during childhood ages 3-12; this establishes timing and communication structure, not coercion"

adultOutcomeTemporalAdjacency : CoverageReceipt
adultOutcomeTemporalAdjacency = coverage-receipt
  prospectiveTemporalIdentification retrospectiveProxy nakamuraEtAl2026
  "retrospectively recalled childhood religious/family experiences were modelled against adulthood religious/relational outcomes in a large Protestant/Catholic congregation sample; the design is cross-sectional secondary analysis, not prospective childhood follow-up"

------------------------------------------------------------------------
-- Missing coordinates remain explicit rather than being inferred from nearby
-- studies.
------------------------------------------------------------------------

record CatholicCoverageFrontier : Set where
  constructor catholic-coverage-frontier
  field
    divinePunishmentFearInstalled : Bool
    parentAutonomySupportInstalled : Bool
    familyTransmissionInstalled : Bool
    apostasyExitTransitionInstalled : Bool
    developmentalTimingInstalled : Bool
    refusalPenaltyInstalled : Bool
    restrictedAlternativesInstalled : Bool
    adultClinicalDistressPTSSInstalled : Bool
    adjustedClinicalAssociationInstalled : Bool
    prospectiveCatholicChildhoodEffectInstalled : Bool

canonicalCatholicCoverageFrontier : CatholicCoverageFrontier
canonicalCatholicCoverageFrontier =
  catholic-coverage-frontier
    true true true true true
    false false false false false

------------------------------------------------------------------------
-- BIDI non-promotions.
------------------------------------------------------------------------

data CatholicSamplePromotesChildhoodCausalEffect : Set where

data PunishmentFearPromotesCoercion : Set where

data BidirectionalCommunicationPromotesAutonomy : Set where

data ApostasyResearchPromotesConstrainedExit : Set where

data RetrospectiveChildhoodRecallPromotesProspectiveRecord : Set where

data CatholicAndProtestantSamplePromotesCatholicOnlyEffect : Set where

data PositiveTransmissionOutcomeRefutesCoercionMechanism : Set where

catholicSampleDoesNotPromoteChildhoodCausalEffect :
  CatholicSamplePromotesChildhoodCausalEffect -> ⊥
catholicSampleDoesNotPromoteChildhoodCausalEffect ()

punishmentFearDoesNotPromoteCoercion : PunishmentFearPromotesCoercion -> ⊥
punishmentFearDoesNotPromoteCoercion ()

bidirectionalCommunicationDoesNotPromoteAutonomy :
  BidirectionalCommunicationPromotesAutonomy -> ⊥
bidirectionalCommunicationDoesNotPromoteAutonomy ()

apostasyResearchDoesNotPromoteConstrainedExit :
  ApostasyResearchPromotesConstrainedExit -> ⊥
apostasyResearchDoesNotPromoteConstrainedExit ()

retrospectiveRecallDoesNotPromoteProspectiveRecord :
  RetrospectiveChildhoodRecallPromotesProspectiveRecord -> ⊥
retrospectiveRecallDoesNotPromoteProspectiveRecord ()

mixedChristianSampleDoesNotPromoteCatholicOnlyEffect :
  CatholicAndProtestantSamplePromotesCatholicOnlyEffect -> ⊥
mixedChristianSampleDoesNotPromoteCatholicOnlyEffect ()

positiveTransmissionOutcomeDoesNotRefuteCoercionMechanism :
  PositiveTransmissionOutcomeRefutesCoercionMechanism -> ⊥
positiveTransmissionOutcomeDoesNotRefuteCoercionMechanism ()

------------------------------------------------------------------------
-- Backward manuscript wording: this is the BIDI return path to John Anthony
-- Brown's proposal.  Partial evidence narrows wording rather than deleting the
-- research programme or pretending the target hypothesis is closed.
------------------------------------------------------------------------

record BrownPaperReturn : Set where
  constructor brown-paper-return
  field
    author : String
    safeCurrentReading : String
    stillMissing : String

currentCatholicInstantiationReturn : BrownPaperReturn
currentCatholicInstantiationReturn = brown-paper-return
  "John Anthony Brown"
  "Catholic-specific evidence now supports selected mechanism coordinates: in a Catholic college sample, perceived parental autonomy support and fear-of-God-punishment-related scrupulosity were associated with religious/spiritual struggle. Childhood Christian family studies also directly establish developmental religious communication and bidirectional child participation. These findings support studying specific relational and sanction coordinates; they do not establish coercive childhood exposure, trauma prevalence, or causal clinical harm."
  "direct Catholic-childhood coercive-exposure measure + refusal/exit restriction + validated adult clinical outcomes + temporally informative design + effect estimate/uncertainty + competing-adversity and residual-confounding audit"

record CatholicInstantiationBoundary : Set where
  constructor catholic-instantiation-boundary
  field
    johnAnthonyBrownAttributionRetained : Bool
    partialCatholicCoordinateCoverageInstalled : Bool
    positiveReligiousDevelopmentEvidenceRetained : Bool
    catholicSampleEqualsCatholicChildhoodCausalEffect : Bool
    fearOfPunishmentEqualsCoercion : Bool
    familyTransmissionEqualsIndoctrination : Bool
    retrospectiveRecallEqualsProspectiveObservation : Bool
    fullH1H5CatholicTargetClosed : Bool

canonicalCatholicInstantiationBoundary : CatholicInstantiationBoundary
canonicalCatholicInstantiationBoundary =
  catholic-instantiation-boundary true true true false false false false false
