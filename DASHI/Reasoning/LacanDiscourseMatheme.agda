module DASHI.Reasoning.LacanDiscourseMatheme where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan

------------------------------------------------------------------------
-- Source calibration: Jacques Lacan, Seminar XVII, The Other Side of
-- Psychoanalysis; Stijn Vanheule, "Capitalist Discourse, Subjectivity and
-- Lacanian Psychoanalysis", DOI 10.3389/fpsyg.2016.01948.
--
-- Exact finite algebra of the four standard discourses.
--
-- Rotation order:
--   Master -> Hysteric -> Analyst -> University -> Master.
------------------------------------------------------------------------

data DiscoursePosition : Set where
  agent other truth product : DiscoursePosition

data StandardDiscourse : Set where
  masterDiscourse hystericDiscourse analystDiscourse universityDiscourse :
    StandardDiscourse

occupant :
  StandardDiscourse →
  DiscoursePosition →
  Lacan.LacanianTerm
occupant masterDiscourse agent = Lacan.masterSignifier
occupant masterDiscourse other = Lacan.knowledgeNetwork
occupant masterDiscourse truth = Lacan.barredSubjectTerm
occupant masterDiscourse product = Lacan.objetATerm

occupant hystericDiscourse agent = Lacan.barredSubjectTerm
occupant hystericDiscourse other = Lacan.masterSignifier
occupant hystericDiscourse truth = Lacan.objetATerm
occupant hystericDiscourse product = Lacan.knowledgeNetwork

occupant analystDiscourse agent = Lacan.objetATerm
occupant analystDiscourse other = Lacan.barredSubjectTerm
occupant analystDiscourse truth = Lacan.knowledgeNetwork
occupant analystDiscourse product = Lacan.masterSignifier

occupant universityDiscourse agent = Lacan.knowledgeNetwork
occupant universityDiscourse other = Lacan.objetATerm
occupant universityDiscourse truth = Lacan.masterSignifier
occupant universityDiscourse product = Lacan.barredSubjectTerm

rotate : StandardDiscourse → StandardDiscourse
rotate masterDiscourse = hystericDiscourse
rotate hystericDiscourse = analystDiscourse
rotate analystDiscourse = universityDiscourse
rotate universityDiscourse = masterDiscourse

rotateFourTimesIsIdentity :
  ∀ discourse →
  rotate (rotate (rotate (rotate discourse))) ≡ discourse
rotateFourTimesIsIdentity masterDiscourse = refl
rotateFourTimesIsIdentity hystericDiscourse = refl
rotateFourTimesIsIdentity analystDiscourse = refl
rotateFourTimesIsIdentity universityDiscourse = refl

orbitAt :
  DiscoursePosition →
  StandardDiscourse →
  List Lacan.LacanianTerm
orbitAt position discourse =
  occupant discourse position
  ∷ occupant (rotate discourse) position
  ∷ occupant (rotate (rotate discourse)) position
  ∷ occupant (rotate (rotate (rotate discourse))) position
  ∷ []

record CompleteMasterOrbit : Set where
  field
    agentOrbit :
      orbitAt agent masterDiscourse
      ≡ Lacan.masterSignifier
      ∷ Lacan.barredSubjectTerm
      ∷ Lacan.objetATerm
      ∷ Lacan.knowledgeNetwork
      ∷ []
    otherOrbit :
      orbitAt other masterDiscourse
      ≡ Lacan.knowledgeNetwork
      ∷ Lacan.masterSignifier
      ∷ Lacan.barredSubjectTerm
      ∷ Lacan.objetATerm
      ∷ []
    truthOrbit :
      orbitAt truth masterDiscourse
      ≡ Lacan.barredSubjectTerm
      ∷ Lacan.objetATerm
      ∷ Lacan.knowledgeNetwork
      ∷ Lacan.masterSignifier
      ∷ []
    productOrbit :
      orbitAt product masterDiscourse
      ≡ Lacan.objetATerm
      ∷ Lacan.knowledgeNetwork
      ∷ Lacan.masterSignifier
      ∷ Lacan.barredSubjectTerm
      ∷ []

canonicalCompleteMasterOrbit : CompleteMasterOrbit
canonicalCompleteMasterOrbit = record
  { agentOrbit = refl
  ; otherOrbit = refl
  ; truthOrbit = refl
  ; productOrbit = refl
  }

record DiscoursePlacementReceipt : Set where
  field
    discourse : StandardDiscourse
    agentTerm : Lacan.LacanianTerm
    otherTerm : Lacan.LacanianTerm
    truthTerm : Lacan.LacanianTerm
    productTerm : Lacan.LacanianTerm
    agentExact : agentTerm ≡ occupant discourse agent
    otherExact : otherTerm ≡ occupant discourse other
    truthExact : truthTerm ≡ occupant discourse truth
    productExact : productTerm ≡ occupant discourse product
    interpretationReceipt : String

masterPlacementReceipt : DiscoursePlacementReceipt
masterPlacementReceipt = record
  { discourse = masterDiscourse
  ; agentTerm = Lacan.masterSignifier
  ; otherTerm = Lacan.knowledgeNetwork
  ; truthTerm = Lacan.barredSubjectTerm
  ; productTerm = Lacan.objetATerm
  ; agentExact = refl
  ; otherExact = refl
  ; truthExact = refl
  ; productExact = refl
  ; interpretationReceipt =
      "Exact standard placement only; application to a speaker, institution or polity requires a separate calibrated bridge."
  }

record LacanDiscourseAuthorityBoundary : Set where
  field
    fourCycleProved : Bool
    everyPositionOrbitExplicit : Bool
    rotationOrderIsMasterHystericAnalystUniversity : Bool
    discoursePlacementDiagnosesSpeaker : Bool
    productPositionAutomaticallyMeasuresSurplus : Bool
    standardDiscourseEqualsCapitalistMutation : Bool
    boundaryNote : String

canonicalLacanDiscourseAuthorityBoundary : LacanDiscourseAuthorityBoundary
canonicalLacanDiscourseAuthorityBoundary = record
  { fourCycleProved = true
  ; everyPositionOrbitExplicit = true
  ; rotationOrderIsMasterHystericAnalystUniversity = true
  ; discoursePlacementDiagnosesSpeaker = false
  ; productPositionAutomaticallyMeasuresSurplus = false
  ; standardDiscourseEqualsCapitalistMutation = false
  ; boundaryNote =
      "The standard four-discourse matheme is a checked Z/4 orbit. Social, clinical and surplus interpretations remain separately calibrated."
  }
