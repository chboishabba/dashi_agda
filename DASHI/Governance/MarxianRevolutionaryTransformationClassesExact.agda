module DASHI.Governance.MarxianRevolutionaryTransformationClassesExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Governance.ComparativeMarxianRevolutionaryTranslationFamilyExact as Family

------------------------------------------------------------------------
-- REUSABLE TRANSFORMATION CLASSES
--
-- These are comparison operators over the existing source-bounded profiles.
-- They do not rank revolutions or assert that a case is exhausted by one class.
------------------------------------------------------------------------

data TransformationClass : Set where
  agrarianisation : TransformationClass
  nationalisation : TransformationClass
  religiousTranslation : TransformationClass
  racialColonialRecoding : TransformationClass
  multiClassCoalition : TransformationClass
  antiImperialistInternationalisation : TransformationClass
  postVictoryStateTransformation : TransformationClass
  ideologicalPluralisation : TransformationClass
  sovereigntyReframing : TransformationClass

record TransformationWitness : Set where
  constructor transformation-witness
  field
    case : Family.RevolutionaryCase
    transform : TransformationClass
    sourceProfile : Family.RevolutionaryTranslationProfile
    reading : String
    exhaustiveOfCase : Bool
    impliesOrthodoxIdentity : Bool
    createsCaseRanking : Bool

open TransformationWitness public

mkWitness :
  Family.RevolutionaryCase →
  TransformationClass →
  Family.RevolutionaryTranslationProfile →
  String →
  TransformationWitness
mkWitness c t p reading =
  transformation-witness c t p reading false false false

iranReligiousTranslation : TransformationWitness
iranReligiousTranslation =
  mkWitness Family.iranCase religiousTranslation Family.iranProfile
    "Marxian/Third-Worldist antagonistic relations are reworked through Shi'i political theology and mostazafin/mostakberin grammar."

vietnamAgrarianisation : TransformationWitness
vietnamAgrarianisation =
  mkWitness Family.vietnamCase agrarianisation Family.vietnamProfile
    "Leninist revolutionary strategy is adapted to a peasant-majority anti-colonial social formation."

chinaAgrarianisation : TransformationWitness
chinaAgrarianisation =
  mkWitness Family.chinaCase agrarianisation Family.chinaProfile
    "Sinification reworks Marxism-Leninism around Chinese agrarian and peasant conditions."

algeriaColonialRecoding : TransformationWitness
algeriaColonialRecoding =
  mkWitness Family.algeriaCase racialColonialRecoding Family.algeriaProfile
    "Class relations are intersected with coloniser/colonised relations in anti-colonial revolutionary thought."

nicaraguaPluralisation : TransformationWitness
nicaraguaPluralisation =
  mkWitness Family.nicaraguaCase ideologicalPluralisation Family.nicaraguaProfile
    "Marxist-Leninist, liberation-theology and social-democratic currents coexist within the revolutionary field."

southAfricaCoalition : TransformationWitness
southAfricaCoalition =
  mkWitness Family.southAfricaCase multiClassCoalition Family.southAfricaProfile
    "Marxist analysis of racialised capitalism is embedded in a multi-class national-democratic strategy."

canonicalWitnesses : List TransformationWitness
canonicalWitnesses =
  iranReligiousTranslation
  ∷ vietnamAgrarianisation
  ∷ chinaAgrarianisation
  ∷ algeriaColonialRecoding
  ∷ nicaraguaPluralisation
  ∷ southAfricaCoalition
  ∷ []

data OneTransformExhaustsCase : Set where
data SameTransformMeansSameOntology : Set where
data TransformationClassCreatesPoliticalEvaluation : Set where

oneTransformDoesNotExhaustCase : OneTransformExhaustsCase → ⊥
oneTransformDoesNotExhaustCase ()

sameTransformDoesNotMeanSameOntology : SameTransformMeansSameOntology → ⊥
sameTransformDoesNotMeanSameOntology ()

transformationClassDoesNotCreatePoliticalEvaluation :
  TransformationClassCreatesPoliticalEvaluation → ⊥
transformationClassDoesNotCreatePoliticalEvaluation ()
