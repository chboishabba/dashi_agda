module DASHI.Education.DigitalESDEfSIndependentDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior

-- EfS-FIRST CARRIER. No import of the Digital seven-principle owner.
-- GreenComp is a policy/reference competency framework, not a causal study.
-- Elliott is a practitioner/theoretical EfS contribution.
-- Vikane/Hoydalsvik is situated Norwegian ECE empirical evidence.
-- None receives intervention-effect or cross-context authority.

data EfSSourceClass : Set where
  competenceReferenceFramework : EfSSourceClass
  practitionerTheory : EfSSourceClass
  situatedEmpiricalStudy : EfSSourceClass

data EfSTheme : Set where
  valuesAndJustice : EfSTheme
  systemsAndProblemFraming : EfSTheme
  possibleFutures : EfSTheme
  participationAndAction : EfSTheme
  ecologicalRelationships : EfSTheme
  educatorEnactmentGap : EfSTheme

data GreenCompArea : Set where
  embodyingSustainabilityValues : GreenCompArea
  embracingComplexity : GreenCompArea
  envisioningSustainableFutures : GreenCompArea
  actingForSustainability : GreenCompArea

data GreenCompCompetence : Set where
  valuingSustainability : GreenCompCompetence
  supportingFairness : GreenCompCompetence
  promotingNature : GreenCompCompetence
  systemsThinking : GreenCompCompetence
  criticalThinking : GreenCompCompetence
  problemFraming : GreenCompCompetence
  futuresLiteracy : GreenCompCompetence
  adaptability : GreenCompCompetence
  exploratoryThinking : GreenCompCompetence
  politicalAgency : GreenCompCompetence
  collectiveAction : GreenCompCompetence
  individualInitiative : GreenCompCompetence

area : GreenCompCompetence → GreenCompArea
area valuingSustainability = embodyingSustainabilityValues
area supportingFairness = embodyingSustainabilityValues
area promotingNature = embodyingSustainabilityValues
area systemsThinking = embracingComplexity
area criticalThinking = embracingComplexity
area problemFraming = embracingComplexity
area futuresLiteracy = envisioningSustainableFutures
area adaptability = envisioningSustainableFutures
area exploratoryThinking = envisioningSustainableFutures
area politicalAgency = actingForSustainability
area collectiveAction = actingForSustainability
area individualInitiative = actingForSustainability

greenCompCompetences : List GreenCompCompetence
greenCompCompetences =
  valuingSustainability ∷ supportingFairness ∷ promotingNature ∷
  systemsThinking ∷ criticalThinking ∷ problemFraming ∷
  futuresLiteracy ∷ adaptability ∷ exploratoryThinking ∷
  politicalAgency ∷ collectiveAction ∷ individualInitiative ∷ []

greenCompURL : String
greenCompURL =
  "https://joint-research-centre.ec.europa.eu/scientific-activities/key-competences-lifelong-learning/greencomp-european-sustainability-competence-framework/greencomp-conceptual-reference-model_en"

record IndependentThemeReceipt : Set where
  constructor independent-theme
  field
    theme : EfSTheme
    sourceReference : String
    sourceClass : EfSSourceClass
    basis : String
    limitation : String
    formulatedWithoutDigitalPrinciple : Bool
    independenceWitness : formulatedWithoutDigitalPrinciple ≡ true
open IndependentThemeReceipt public

valuesReceipt : IndependentThemeReceipt
valuesReceipt = independent-theme valuesAndJustice greenCompURL
  competenceReferenceFramework
  "GreenComp: valuing sustainability and supporting fairness; values are open to reflection."
  "Competence specification, not evidence that a given digital intervention teaches values."
  true refl

systemsReceipt : IndependentThemeReceipt
systemsReceipt = independent-theme systemsAndProblemFraming greenCompURL
  competenceReferenceFramework
  "GreenComp: systems thinking, critical thinking and problem framing."
  "Framework descriptors do not establish measured systems understanding."
  true refl

futureReceipt : IndependentThemeReceipt
futureReceipt = independent-theme possibleFutures greenCompURL
  competenceReferenceFramework
  "GreenComp: futures literacy, adaptability and exploratory thinking."
  "Futures scenario production does not imply future outcomes."
  true refl

collectiveReceipt : IndependentThemeReceipt
collectiveReceipt = independent-theme participationAndAction greenCompURL
  competenceReferenceFramework
  "GreenComp: political agency, collective action and individual initiative."
  "Participation and stated intention are not demonstrated agency or action."
  true refl

ecologicalReceipt : IndependentThemeReceipt
ecologicalReceipt = independent-theme ecologicalRelationships
  (Prior.EfSSource.exactLocator Prior.elliottEfS)
  practitionerTheory
  "Elliott: ecological relations, critical reflection and child participation in sustainability."
  "A practitioner-theoretical account is not an intervention or general prevalence estimate."
  true refl

enactmentReceipt : IndependentThemeReceipt
enactmentReceipt = independent-theme educatorEnactmentGap
  (Prior.EfSSource.exactLocator Prior.vikaneHoydalsvik)
  situatedEmpiricalStudy
  "Situated teacher-understanding versus transformative-practice problem in Norwegian ECE."
  "Neither causal explanation nor automatic transfer to other ages, countries, or digital delivery."
  true refl

independentlyNominatedThemes : List IndependentThemeReceipt
independentlyNominatedThemes =
  valuesReceipt ∷ systemsReceipt ∷ futureReceipt ∷ collectiveReceipt ∷
  ecologicalReceipt ∷ enactmentReceipt ∷ []

-- The source-derived competency labels, the grouping into our six candidate
-- study themes, and a digital crosswalk have different origins/claim ceilings.
data SixThemesAreUniquelyDeterminedBySources : Set where
data CompetencyFrameworkProvesEffect : Set where
data IndependentFormalDerivationIsIndependentHumanCoding : Set where

noUniqueSixThemeClaim : SixThemesAreUniquelyDeterminedBySources → ⊥
noUniqueSixThemeClaim ()
noCompetenceEffectPromotion : CompetencyFrameworkProvesEffect → ⊥
noCompetenceEffectPromotion ()
noHumanCodingPromotion : IndependentFormalDerivationIsIndependentHumanCoding → ⊥
noHumanCodingPromotion ()
