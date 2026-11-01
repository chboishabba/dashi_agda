module DASHI.Governance.ComparativeMarxianRevolutionaryTranslationFamilyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Governance.ComparativeMarxianRevolutionaryTranslationSourceAtlasExact as Sources
import DASHI.Governance.IranianDialecticalTransportPhilosophyCrossPollinationExact as Iran
import DASHI.Governance.IranianRevolutionaryFieldTransportCapstoneExact as IranCapstone

------------------------------------------------------------------------
-- COMPARATIVE TRANSLATION FAMILY
--
-- The family compares how Marxian/Leninist relations are locally translated.
-- A translation may change revolutionary subject, national frame, religious
-- ontology, class coalition, state form or historical horizon.  Comparison
-- neither ranks cases nor identifies them.
------------------------------------------------------------------------

data RevolutionaryCase : Set where
  iranCase : RevolutionaryCase
  vietnamCase : RevolutionaryCase
  chinaCase : RevolutionaryCase
  algeriaCase : RevolutionaryCase
  nicaraguaCase : RevolutionaryCase
  southAfricaCase : RevolutionaryCase

data TranslationAxis : Set where
  revolutionarySubjectAxis : TranslationAxis
  nationalLiberationAxis : TranslationAxis
  classCoalitionAxis : TranslationAxis
  peasantRoleAxis : TranslationAxis
  religiousOntologyAxis : TranslationAxis
  racialColonialAxis : TranslationAxis
  stateBuildingAxis : TranslationAxis
  internationalismAxis : TranslationAxis
  pluralIdeologyAxis : TranslationAxis

record RevolutionaryTranslationProfile : Set where
  constructor revolutionary-translation-profile
  field
    case : RevolutionaryCase
    primarySource : String
    revolutionarySubject : String
    nationalFrame : String
    classCoalition : String
    peasantRole : String
    religiousOrNormativeTranslation : String
    colonialRacialRelation : String
    stateBuildingRelation : String
    internationalismRelation : String
    pluralityResidual : String
    marxianGrammarPresent : Bool
    localTranslationPresent : Bool
    translationEqualsOrthodoxMarxism : Bool
    oneCaseDeterminesAnother : Bool
    caseRankingCreated : Bool

open RevolutionaryTranslationProfile public

iranProfile : RevolutionaryTranslationProfile
iranProfile = revolutionary-translation-profile
  iranCase
  "Iranian revolutionary intellectual genealogy + Shariati/Khomeini source owners"
  "mostazafin / oppressed subject plus Islamic revolutionary constituency"
  "anti-imperialist sovereignty and Islamic revolutionary order"
  "class grammar translated into a wider oppressed/oppressor moral-political field"
  "not the sole revolutionary subject"
  "Shi'i political theology and Islamic-humanist revolutionary ontology"
  "anti-colonial / anti-hegemonic relation"
  "jurist-led Islamic state; not proletarian sovereignty"
  "solidarity of oppressed / resistance field"
  "Marxian, Islamic, nationalist and Third-Worldist strands remain distinguishable"
  true true false false false

vietnamProfile : RevolutionaryTranslationProfile
vietnamProfile = revolutionary-translation-profile
  vietnamCase
  "Fadaee 2026 + Red Internationalism 2023 + McHale 2010"
  "workers-and-peasants revolutionary bloc with peasantry fundamental in local conditions"
  "national independence joined to communist revolution"
  "Leninist two-stage strategy plus broad coalition-building"
  "fundamental revolutionary role in a predominantly peasant society"
  "no religious ontology required by the profile; Confucian and national inheritances remain historical residuals"
  "French colonial domination and later anti-imperialist struggle"
  "national liberation followed by socialist/communist state-building"
  "Leninist self-determination in tension with universal communist emancipation"
  "Vietnamese Marxism remains non-monolithic; dissent and contingency retained"
  true true false false false

chinaProfile : RevolutionaryTranslationProfile
chinaProfile = revolutionary-translation-profile
  chinaCase
  "Wylie on Sinification + Cambridge History peasant movements"
  "party-army / peasant-centred revolutionary mobilisation"
  "Chinese national and revolutionary transformation"
  "Marxism-Leninism adapted to weak capitalist development and rural social structure"
  "central rather than auxiliary in revolutionary strategy"
  "Chinese historical/cultural inheritance retained as translation context"
  "semi-colonial / imperial domination and landlord relations"
  "party-state construction after revolutionary victory"
  "international Marxism translated into Chinese historical conditions"
  "adaptation and rupture remain visible rather than one orthodox invariant"
  true true false false false

algeriaProfile : RevolutionaryTranslationProfile
algeriaProfile = revolutionary-translation-profile
  algeriaCase
  "Mackinnon 2023 + Fanon revolutionary source lane"
  "colonised national subject and revolutionary liberation movement"
  "anti-colonial national liberation"
  "class analysis intersects coloniser/colonised relation"
  "rural and colonised masses not reducible to European proletarian model"
  "Fanonian humanism and anti-colonial political thought"
  "French colonial domination"
  "postcolonial state-building is a distinct downstream problem"
  "Third-World anti-colonial internationalism"
  "Fanon and FLN-related thought not collapsed into one doctrine"
  true true false false false

nicaraguaProfile : RevolutionaryTranslationProfile
nicaraguaProfile = revolutionary-translation-profile
  nicaraguaCase
  "Jarquín 2021"
  "plural anti-Somoza revolutionary coalition"
  "national revolution"
  "Marxist-Leninist strands coexist with other revolutionary constituencies"
  "rural/popular mobilisation is case-specific"
  "liberation theology coexists with Marxist and social-democratic currents"
  "dictatorship, class inequality and external intervention"
  "revolutionary government and survival under external pressure"
  "Cuban and wider revolutionary international connections"
  "plurality is constitutive; FSLN leaders themselves differed over Marxism's applicability"
  true true false false false

southAfricaProfile : RevolutionaryTranslationProfile
southAfricaProfile = revolutionary-translation-profile
  southAfricaCase
  "McKinley on ANC Marxism"
  "racially oppressed national majority with asserted working-class leadership"
  "national democratic revolution"
  "multi-class revolutionary front"
  "not the primary defining axis"
  "no single religious translation; national-democratic and Marxist registers coexist"
  "colonial dispossession plus racialised capitalism / colonialism of a special type"
  "nation-building without automatic socialist transition"
  "anti-colonial / socialist internationalism through ANC-SACP histories"
  "national liberation and socialism remain related but non-identical horizons"
  true true false false false

canonicalProfiles : List RevolutionaryTranslationProfile
canonicalProfiles =
  iranProfile ∷ vietnamProfile ∷ chinaProfile ∷ algeriaProfile
  ∷ nicaraguaProfile ∷ southAfricaProfile ∷ []

data SameMarxianGrammarMeansSameRevolution : Set where
data PeasantCentralityMeansMaoism : Set where
data NationalLiberationMeansSocialism : Set where
data ReligiousParticipationMeansTheocracy : Set where
data ComparisonCreatesPoliticalRecommendation : Set where

sameMarxianGrammarDoesNotMeanSameRevolution :
  SameMarxianGrammarMeansSameRevolution → ⊥
sameMarxianGrammarDoesNotMeanSameRevolution ()

peasantCentralityDoesNotDefinitionallyMeanMaoism :
  PeasantCentralityMeansMaoism → ⊥
peasantCentralityDoesNotDefinitionallyMeanMaoism ()

nationalLiberationDoesNotDefinitionallyMeanSocialism :
  NationalLiberationMeansSocialism → ⊥
nationalLiberationDoesNotDefinitionallyMeanSocialism ()

religiousParticipationDoesNotDefinitionallyMeanTheocracy :
  ReligiousParticipationMeansTheocracy → ⊥
religiousParticipationDoesNotDefinitionallyMeanTheocracy ()

comparisonDoesNotCreatePoliticalRecommendation :
  ComparisonCreatesPoliticalRecommendation → ⊥
comparisonDoesNotCreatePoliticalRecommendation ()

------------------------------------------------------------------------
-- Positive family theorem: local translation is represented in every selected
-- case while orthodox identity and cross-case determination remain blocked.
------------------------------------------------------------------------

record TranslationFamilyReceipt : Set where
  constructor translation-family-receipt
  field
    profiles : List RevolutionaryTranslationProfile
    iranMediatedFieldTransport : IranCapstone.RevolutionaryFieldTransport
    everySelectedCaseHasLocalTranslation : Bool
    noSelectedCaseIsDeclaredOrthodoxInvariant : Bool
    noCaseRanksAnother : Bool
    pluralityAndProcessHistoryRetained : Bool

canonicalFamilyReceipt : TranslationFamilyReceipt
canonicalFamilyReceipt =
  translation-family-receipt
    canonicalProfiles
    IranCapstone.canonicalRevolutionaryFieldTransport
    true true true true
