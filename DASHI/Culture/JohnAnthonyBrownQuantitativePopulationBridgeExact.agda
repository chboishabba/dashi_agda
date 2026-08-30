module DASHI.Culture.JohnAnthonyBrownQuantitativePopulationBridgeExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: QUANTITATIVE TARGET-POPULATION BRIDGE
--
-- Authorial programme source: John Anthony Brown.
--
-- This owner installs quantitative studies that are materially closer to H1/H5
-- than generic religiosity or trauma comparators, while retaining exact scope.
-- The strongest presently recovered studies concern conversion/change efforts
-- in sexual/gender-minority populations; they are not silently generalized to
-- all childhood religious formation or to Catholic childhood specifically.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

record QuantitativeBridgeSource : Set where
  constructor quantitative-bridge-source
  field
    sourceKey : String
    authors : String
    title : String
    year : String
    venue : String
    doiOrIdentifier : String
    population : String
    exposure : String
    outcome : String
    design : String
    estimate : String
    confoundingSurface : String
    boundedRole : String
    childhoodOrAdolescentExposure : Bool
    religiousProviderExplicit : Bool
    catholicSpecific : Bool
    generalReligiousFormationSample : Bool

open QuantitativeBridgeSource public

ryanEtAl2020 : QuantitativeBridgeSource
ryanEtAl2020 = quantitative-bridge-source
  "ryan-toomey-diaz-russell-2020-parent-soce"
  "Caitlin Ryan; Russell B. Toomey; Rafael M. Diaz; Stephen T. Russell"
  "Parent-Initiated Sexual Orientation Change Efforts With LGBT Adolescents: Implications for Young Adult Mental Health and Adjustment"
  "2020 (published online 2018)"
  "Journal of Homosexuality 67(2):159-173"
  "10.1080/00918369.2018.1538407"
  "245 White and Latino LGBT young adults aged 21-25"
  "retrospectively reported parent/caregiver efforts during adolescence, including being sent to therapists or religious leaders for conversion interventions"
  "depression, suicidal thoughts, suicide attempts, educational attainment, weekly income"
  "cross-sectional young-adult survey with retrospective adolescent exposure"
  "paper reports adverse outcome associations; exact coefficient vector should be recovered from full tables before numeric theorem installation"
  "bounded to parent-initiated adolescent sexual-orientation change efforts; unusually close family-authority/developmental evidence but not ordinary religious upbringing and not Catholic-specific"
  true true false false

blosnichEtAl2020 : QuantitativeBridgeSource
blosnichEtAl2020 = quantitative-bridge-source
  "blosnich-henderson-coulter-goldbach-meyer-2020-soce-ace"
  "John R. Blosnich; Emmett R. Henderson; Robert W. S. Coulter; Jeremy T. Goldbach; Ilan H. Meyer"
  "Sexual Orientation Change Efforts, Adverse Childhood Experiences, and Suicide Ideation and Attempt Among Sexual Minority Adults, United States, 2016-2018"
  "2020"
  "American Journal of Public Health 110(7):1024-1030"
  "10.2105/AJPH.2020.305637"
  "nationally representative sample of 1518 nontransgender sexual-minority US adults"
  "lifetime sexual-orientation change efforts; 80.8% of exposed participants reported a religious leader as provider"
  "lifetime suicidal ideation, suicide planning, suicide attempts"
  "weighted cross-sectional regression adjusting for demographics and adverse childhood experiences"
  "SOCE exposure associated with nearly twice the odds of lifetime suicidal ideation, 75% increased odds of planning, and 88% increased odds of an attempt with minor injury"
  "ACE adjustment installed; observational and retrospective exposure remains vulnerable to residual confounding and does not establish a general childhood-religion causal effect"
  "strong quantitative religion-provider adjacency and explicit competing-adversity adjustment; exposure timing is lifetime rather than necessarily childhood and the population is sexual-minority adults"
  false true false false

greenEtAl2020 : QuantitativeBridgeSource
greenEtAl2020 = quantitative-bridge-source
  "green-price-feeney-dorison-pick-2020-sogice-youth"
  "Amy E. Green; Myeshia Price-Feeney; Samuel H. Dorison; Casey J. Pick"
  "Self-Reported Conversion Efforts and Suicidality Among US LGBTQ Youths and Young Adults, 2018"
  "2020"
  "American Journal of Public Health 110(8):1221-1227"
  "10.2105/AJPH.2020.305701"
  "US LGBTQ participants aged 13-24"
  "self-reported sexual-orientation or gender-identity conversion efforts"
  "suicidality"
  "cross-sectional online survey with multivariable logistic regression"
  "study reports higher suicidality among participants exposed to conversion efforts; exact estimate vector should remain source-table specific"
  "models adjusted for age, race/ethnicity, geography, parents' religiously negative LGBTQ messaging, identity, discrimination, and physical threats/harm"
  "direct youth/young-adult quantitative evidence, but conversion efforts are a special coercive practice rather than ordinary religious formation"
  true false false false

tranEtAl2024 : QuantitativeBridgeSource
tranEtAl2024 = quantitative-bridge-source
  "tran-et-al-2024-pride-conversion-mental-health"
  "Nguyen K. Tran; Elle Lett; Barbara Cassese; Carl G. Streed Jr; David J. Kinitz; Shalonda Ingram; Karalin Sprague; Zubin Dastur; Micah E. Lubensky; Annesa Flentje; Juno Obedin-Maliver; Mitchell R. Lunn"
  "Conversion practice recall and mental health symptoms in sexual and gender minority adults in the USA: a cross-sectional study"
  "2024"
  "The Lancet Psychiatry 11(11):879-889"
  "10.1016/S2215-0366(24)00251-7"
  "4426 US sexual- and gender-minority adults aged 18-84"
  "lifetime recalled conversion practice targeting sexual orientation, gender identity, or both"
  "GAD-7, PHQ-9, PCL-6 PTSD symptoms, SBQ-R suicidality"
  "cross-sectional analysis nested in the prospective PRIDE cohort; exposure history and outcomes measured on separate questionnaires"
  "both-form exposure: PTSD beta 2.84 (95% CI 0.94-4.74), suicidality beta 2.14 (0.95-3.32); sexual-orientation-only exposure: PTSD beta 1.10 (0.22-1.98)"
  "regression controlled demographic and childhood factors; sensitivity analyses reported moderate robustness to potential unmeasured confounding"
  "important quantitative H1/H5-adjacent association evidence with uncertainty and sensitivity analysis, but not childhood-specific, not religion-only, and not Catholic-specific"
  false false false false

okaGorenGulmez2025 : QuantitativeBridgeSource
okaGorenGulmez2025 = quantitative-bridge-source
  "oka-goren-gulmez-2025-muslim-religious-trauma-scale"
  "Uzeyir Oka; Ayse Burcu Goren; Cigdem Gulmez"
  "Construction and Validation of a Muslim Religious Trauma Scale"
  "2025"
  "Journal of Loss and Trauma 30(2):167-196"
  "10.1080/15325024.2024.2412294"
  "452 Muslim participants in Turkey aged 18-60 or over"
  "self-reported traumatic religious experiences measured by a newly developed Muslim Religious Trauma Scale"
  "post-traumatic symptoms, dissociation, subjective happiness, general trauma and religiosity measures"
  "cross-sectional online psychometric validation with exploratory factor analysis"
  "concurrent-validity associations were reported with general trauma, post-traumatic symptoms and dissociation; effect-size table remains to be separately extracted"
  "instrument validation/concurrent validity, not longitudinal causal identification"
  "direct quantitative religious-trauma construct evidence in a Muslim population; valuable transport comparison but not Christian/Catholic or childhood-specific"
  false false false false

------------------------------------------------------------------------
-- Relation to John Anthony Brown H1/H5.
------------------------------------------------------------------------

data BridgeFit : Set where
  directPopulationAdjacency
  developmentalFamilyAdjacency
  religionProviderAdjacency
  constructInstrumentAdjacency
  comparatorOnly : BridgeFit

record QuantitativeHypothesisBridge : Set where
  constructor quantitative-hypothesis-bridge
  field
    source : QuantitativeBridgeSource
    hypothesis : Manifest.HypothesisKey
    fit : BridgeFit
    associationCoordinateInstalled : Bool
    targetPopulationClosed : Bool
    causalCoordinateInstalled : Bool
    reading : String

open QuantitativeHypothesisBridge public

ryanH1Bridge : QuantitativeHypothesisBridge
ryanH1Bridge = quantitative-hypothesis-bridge
  ryanEtAl2020 Manifest.H1 developmentalFamilyAdjacency true false false
  "Parent-initiated adolescent change efforts supply a real family-authority/developmental exposure-outcome association, but the exposure is sexual-orientation change effort and cannot be substituted for general coercive religious socialisation."

blosnichH5Bridge : QuantitativeHypothesisBridge
blosnichH5Bridge = quantitative-hypothesis-bridge
  blosnichEtAl2020 Manifest.H5 religionProviderAdjacency true false false
  "Association remains after explicit ACE adjustment in a sexual-minority adult sample; this is methodologically relevant to H5 but does not establish absence of residual confounding or John Anthony Brown's full target-domain effect."

tranH1Bridge : QuantitativeHypothesisBridge
tranH1Bridge = quantitative-hypothesis-bridge
  tranEtAl2024 Manifest.H1 directPopulationAdjacency true false false
  "PTSD symptom associations with conversion-practice recall provide a bounded quantitative analogue to H1, with confidence intervals and sensitivity analysis; childhood timing and religious-provider restriction are not guaranteed."

okaH1InstrumentBridge : QuantitativeHypothesisBridge
okaH1InstrumentBridge = quantitative-hypothesis-bridge
  okaGorenGulmez2025 Manifest.H1 constructInstrumentAdjacency true false false
  "A religion-specific trauma instrument can correlate with post-traumatic symptoms, demonstrating quantitative measurability without transporting Muslim-population factor structure or effect sizes to Catholic childhood."

------------------------------------------------------------------------
-- Exact non-promotions.
------------------------------------------------------------------------

data ConversionPracticePromotesGeneralReligiousFormation : Set where

data ReligiousLeaderProviderPromotesReligionAsSoleCause : Set where

data ACEAdjustedAssociationPromotesNoResidualConfounding : Set where

data YouthAssociationPromotesAdultLongitudinalEffect : Set where

data MuslimReligiousTraumaScalePromotesCatholicValidity : Set where

data QuantitativeAssociationPromotesLegalOrNormativeConclusion : Set where

conversionPracticeDoesNotPromoteGeneralReligiousFormation :
  ConversionPracticePromotesGeneralReligiousFormation → ⊥
conversionPracticeDoesNotPromoteGeneralReligiousFormation ()

religiousLeaderProviderDoesNotPromoteReligionAsSoleCause :
  ReligiousLeaderProviderPromotesReligionAsSoleCause → ⊥
religiousLeaderProviderDoesNotPromoteReligionAsSoleCause ()

aceAdjustmentDoesNotPromoteNoResidualConfounding :
  ACEAdjustedAssociationPromotesNoResidualConfounding → ⊥
aceAdjustmentDoesNotPromoteNoResidualConfounding ()

youthAssociationDoesNotPromoteAdultLongitudinalEffect :
  YouthAssociationPromotesAdultLongitudinalEffect → ⊥
youthAssociationDoesNotPromoteAdultLongitudinalEffect ()

muslimScaleDoesNotPromoteCatholicValidity :
  MuslimReligiousTraumaScalePromotesCatholicValidity → ⊥
muslimScaleDoesNotPromoteCatholicValidity ()

quantitativeAssociationDoesNotPromoteLegalOrNormativeConclusion :
  QuantitativeAssociationPromotesLegalOrNormativeConclusion → ⊥
quantitativeAssociationDoesNotPromoteLegalOrNormativeConclusion ()

record QuantitativePopulationBridgeBoundary : Set where
  constructor quantitative-population-bridge-boundary
  field
    johnAnthonyBrownProgrammeRetained : Bool
    quantitativeTargetAdjacentEvidenceInstalled : Bool
    familyAdolescentExposureEvidenceInstalled : Bool
    aceAdjustedEvidenceInstalled : Bool
    effectEstimateWithUncertaintyInstalled : Bool
    conversionPracticeEqualsGeneralReligiousFormation : Bool
    religiousProviderEqualsSoleCause : Bool
    adjustmentEqualsNoResidualConfounding : Bool
    christianOrMuslimEvidenceEqualsCatholicSpecificity : Bool
    directCatholicChildhoodLongitudinalEffectStillMissing : Bool

canonicalQuantitativePopulationBridgeBoundary : QuantitativePopulationBridgeBoundary
canonicalQuantitativePopulationBridgeBoundary =
  quantitative-population-bridge-boundary
    true true true true true false false false false true
