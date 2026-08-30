module DASHI.Culture.JohnAnthonyBrownPrimarySourceVerificationExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: PRIMARY-SOURCE / INSTRUMENT VERIFICATION ATLAS
--
-- Authorial programme source: John Anthony Brown.
--
-- This owner is downstream of the manuscript/hypothesis atlas.  It records
-- externally recovered sources with title/author/year/venue/DOI and a bounded
-- evidential role.  A verified scholarly source is not thereby the right source
-- for every hypothesis coordinate or target population.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

record VerifiedSource : Set where
  constructor verified-source
  field
    sourceKey : String
    authors : String
    title : String
    year : String
    venue : String
    doiOrIdentifier : String
    verifiedLocator : String
    boundedRole : String
    targetPopulationMatch : Bool
    childhoodExposureDirect : Bool
    catholicSpecific : Bool

open VerifiedSource public

------------------------------------------------------------------------
-- H3: institutional betrayal construct / instrument layer.
------------------------------------------------------------------------

smithFreyd2014 : VerifiedSource
smithFreyd2014 = verified-source
  "smith-freyd-2014-institutional-betrayal"
  "Carly P. Smith; Jennifer J. Freyd"
  "Institutional betrayal"
  "2014"
  "American Psychologist 69(6):575-587"
  "10.1037/a0037564"
  "APA DOI record"
  "construct/framework source for institutional betrayal; examples include schools, churches, military and government; not a target-population effect estimate for John Anthony Brown H3"
  false false false

reffiPinciottiOrcutt2021 : VerifiedSource
reffiPinciottiOrcutt2021 = verified-source
  "reffi-pinciotti-orcutt-2021-ibq2"
  "Anthony N. Reffi; Caitlin M. Pinciotti; Holly K. Orcutt"
  "Psychometric Properties of the Institutional Betrayal Questionnaire, Version 2: Evidence for a Two-Factor Model"
  "2021"
  "Journal of Interpersonal Violence 36(11-12):5659-5684"
  "10.1177/0886260518805771"
  "PubMed PMID 30328380 / SAGE DOI record"
  "IBQ.2 construct-validity/factor-structure evidence in adult sexual-assault survivors; instrument candidate for institutional-betrayal measurement, not religious-childhood validation"
  false false false

monteithEtAl2021 : VerifiedSource
monteithEtAl2021 = verified-source
  "monteith-et-al-2021-ibq2-military"
  "Lindsey L. Monteith; Alexandra L. Schneider; Ryan Holliday; Nazanin H. Bahraini"
  "Assessing Institutional Betrayal Among Female Veterans Who Experienced Military Sexual Trauma: A Rasch Analysis of the Institutional Betrayal Questionnaire.2"
  "2021"
  "Journal of Interpersonal Violence 36(23-24):10861-10883"
  "10.1177/0886260520983959"
  "PubMed PMID 33403916"
  "cross-population psychometric evidence for IBQ.2 in military-sexual-trauma survivors; demonstrates transport cannot be assumed from one institution to another"
  false false false

------------------------------------------------------------------------
-- H2: autonomy / spiritual-distress measurement candidates.
------------------------------------------------------------------------

weinsteinPrzybylskiRyan2012 : VerifiedSource
weinsteinPrzybylskiRyan2012 = verified-source
  "weinstein-przybylski-ryan-2012-iaf"
  "Netta Weinstein; Andrew K. Przybylski; Richard M. Ryan"
  "The index of autonomous functioning: Development of a scale of human autonomy"
  "2012"
  "Journal of Research in Personality 46(4):397-413"
  "10.1016/j.jrp.2012.03.007"
  "Elsevier DOI / University of Essex repository"
  "validated adult trait-autonomy measure with authorship/self-congruence, interest-taking and low susceptibility to control; candidate for H2 autonomy coordinate, not validation in religious-trauma populations"
  false false false

ellison1983 : VerifiedSource
ellison1983 = verified-source
  "ellison-1983-spiritual-wellbeing"
  "Craig W. Ellison"
  "Spiritual Well-Being: Conceptualization and Measurement"
  "1983"
  "Journal of Psychology and Theology 11(4)"
  "10.1177/009164718301100406"
  "SAGE DOI record"
  "source describing the Paloutzian-Ellison Spiritual Well-Being Scale and its religious/existential dimensions; candidate H2 spiritual-wellbeing measure, not a coercion-specific trauma instrument"
  false false false

exlineEtAl2014 : VerifiedSource
exlineEtAl2014 = verified-source
  "exline-pargament-grubbs-yali-2014-rss"
  "Julie J. Exline; Kenneth I. Pargament; Joshua B. Grubbs; Ann Marie Yali"
  "The Religious and Spiritual Struggles Scale: Development and initial validation"
  "2014"
  "Psychology of Religion and Spirituality 6(3):208-222"
  "10.1037/a0036465"
  "APA DOI record"
  "validated multidimensional religious/spiritual-struggle measure covering divine, demonic, interpersonal, moral, doubt and ultimate-meaning struggles; relevant to H2 spiritual-distress coordinates but not equivalent to coercive religious exposure"
  false false false

koch2022 : VerifiedSource
koch2022 = verified-source
  "koch-2022-spiritual-harm-abuse-scale"
  "Daniel Koch"
  "Development of the Spiritual Harm and Abuse Scale"
  "2022"
  "Journal for the Scientific Study of Religion"
  "10.1111/jssr.12792"
  "Wiley DOI record"
  "scale-development source for spiritual harm/abuse; candidate construct/instrument bridge closer to coercive religious experience than generic religiosity, while still not a childhood-Catholic validation"
  false false false

spiritualSafety2026 : VerifiedSource
spiritualSafety2026 = verified-source
  "spiritual-safety-2026-s-safe"
  "Lianna McMinn et al."
  "Development and Psychometric Validation of the Spiritual Safety Scale (S-SAFE): A Measure for Psychological Safety and Spiritual Abuse in North American Christian Communities"
  "2026"
  "Journal of Religion and Health"
  "10.1007/s10943-026-02734-y"
  "PubMed PMID 42474978"
  "psychometrically validated spiritual-safety/spiritual-abuse measure in primarily North American Christian samples; promising construct/instrument candidate but not direct childhood-Catholic H1/H5 evidence"
  false false false

------------------------------------------------------------------------
-- Direct but bounded qualitative target-domain bridge.
------------------------------------------------------------------------

richardsMcKinzieUnderwood2026 : VerifiedSource
richardsMcKinzieUnderwood2026 = verified-source
  "richards-mckinzie-underwood-2026-self-authorship"
  "Patricia Richards; Ashleigh McKinzie; Jasmine Underwood"
  "From Embodied Contradictions to Self-Authorship: Survivors of Abuse Leaving Evangelical Churches"
  "2026"
  "Qualitative Sociology 49:293-316"
  "10.1007/s11133-025-09629-6"
  "Springer DOI record"
  "qualitative interviews with adult survivors of abuse in white evangelical contexts; documents childhood hell fear, submission, distrust of bodily intuition, institutional betrayal, exit difficulty and later self-authorship. Strong mechanism/meaning bridge, not prevalence/effect-size evidence and not Catholic-specific"
  true true false

------------------------------------------------------------------------
-- Hypothesis-coordinate mapping.  Verification is source-specific and does not
-- close a hypothesis automatically.
------------------------------------------------------------------------

data EvidenceCoordinate : Set where
  constructCoordinate
  instrumentCoordinate
  populationCoordinate
  associationCoordinate
  causalCoordinate
  qualitativeMeaningCoordinate
  recoveryCoordinate : EvidenceCoordinate

record SourceToHypothesis : Set where
  constructor source-to-hypothesis
  field
    source : VerifiedSource
    hypothesis : Manifest.HypothesisKey
    coordinate : EvidenceCoordinate
    installedAtBoundedScope : Bool
    reading : String

open SourceToHypothesis public

h3InstitutionalBetrayalConstruct : SourceToHypothesis
h3InstitutionalBetrayalConstruct = source-to-hypothesis
  smithFreyd2014 Manifest.H3 constructCoordinate true
  "institutional betrayal is an established construct; this does not establish its incremental effect in John Anthony Brown's proposed target population"

h3InstitutionalBetrayalInstrument : SourceToHypothesis
h3InstitutionalBetrayalInstrument = source-to-hypothesis
  reffiPinciottiOrcutt2021 Manifest.H3 instrumentCoordinate true
  "IBQ.2 has psychometric evidence in adult sexual-assault survivors; religious-childhood measurement invariance/validity remains open"

h2AutonomyInstrument : SourceToHypothesis
h2AutonomyInstrument = source-to-hypothesis
  weinsteinPrzybylskiRyan2012 Manifest.H2 instrumentCoordinate true
  "IAF is a validated autonomy measure and a candidate H2 instrument; target-population validity and conceptual fit to perceived childhood religious coercion remain study-design questions"

h2SpiritualStruggleInstrument : SourceToHypothesis
h2SpiritualStruggleInstrument = source-to-hypothesis
  exlineEtAl2014 Manifest.H2 instrumentCoordinate true
  "RSS supports a multidimensional spiritual-struggle coordinate; it must not be substituted for a coercion exposure measure"

h1QualitativeTargetBridge : SourceToHypothesis
h1QualitativeTargetBridge = source-to-hypothesis
  richardsMcKinzieUnderwood2026 Manifest.H1 qualitativeMeaningCoordinate true
  "direct qualitative survivor evidence supports mechanism/meaning plausibility around childhood hell fear, abuse, authority, institutional betrayal and exit; it does not provide H1's longitudinal population effect estimate"

h2QualitativeAutonomyBridge : SourceToHypothesis
h2QualitativeAutonomyBridge = source-to-hypothesis
  richardsMcKinzieUnderwood2026 Manifest.H2 qualitativeMeaningCoordinate true
  "the survivor study explicitly theorizes movement toward bodily autonomy/self-authorship after exit, but this is qualitative and selected-sample evidence rather than a population-average autonomy effect"

------------------------------------------------------------------------
-- Core BIDI non-promotions.
------------------------------------------------------------------------

data VerifiedInstrumentPromotesTargetPopulationValidity : Set where

data QualitativeMechanismPromotesPopulationEffectSize : Set where

data SpiritualStrugglePromotesCoerciveExposure : Set where

data InstitutionalBetrayalConstructPromotesIncrementalH3Effect : Set where

data ChristianSamplePromotesCatholicSpecificity : Set where

verifiedInstrumentDoesNotPromoteTargetPopulationValidity :
  VerifiedInstrumentPromotesTargetPopulationValidity → ⊥
verifiedInstrumentDoesNotPromoteTargetPopulationValidity ()

qualitativeMechanismDoesNotPromotePopulationEffectSize :
  QualitativeMechanismPromotesPopulationEffectSize → ⊥
qualitativeMechanismDoesNotPromotePopulationEffectSize ()

spiritualStruggleDoesNotPromoteCoerciveExposure :
  SpiritualStrugglePromotesCoerciveExposure → ⊥
spiritualStruggleDoesNotPromoteCoerciveExposure ()

institutionalBetrayalConstructDoesNotPromoteIncrementalH3Effect :
  InstitutionalBetrayalConstructPromotesIncrementalH3Effect → ⊥
institutionalBetrayalConstructDoesNotPromoteIncrementalH3Effect ()

christianSampleDoesNotPromoteCatholicSpecificity :
  ChristianSamplePromotesCatholicSpecificity → ⊥
christianSampleDoesNotPromoteCatholicSpecificity ()

record PrimarySourceVerificationBoundary : Set where
  constructor primary-source-verification-boundary
  field
    authorialProgrammeAttributedToJohnAnthonyBrown : Bool
    verifiedSourcesCarryDOIWhenRecovered : Bool
    sourceRoleSeparatedFromSourceQuality : Bool
    instrumentValidityEqualsTargetPopulationValidity : Bool
    qualitativeEvidenceEqualsPopulationEffectSize : Bool
    religiousSpiritualStruggleEqualsCoerciveExposure : Bool
    institutionalBetrayalConstructEqualsH3IncrementalEffect : Bool
    christianEvidenceEqualsCatholicSpecificEvidence : Bool
    directReligiousChildhoodEvidenceStillNeeded : Bool

canonicalPrimarySourceVerificationBoundary : PrimarySourceVerificationBoundary
canonicalPrimarySourceVerificationBoundary =
  primary-source-verification-boundary
    true true true false false false false false true
