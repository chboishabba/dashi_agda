module DASHI.Culture.AnthropologyDisciplineCoverageOwnerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Culture.AnthropologyEthnographicFieldworkReceiptExact as Fieldwork

------------------------------------------------------------------------
-- MINIMAL ANTHROPOLOGY DISCIPLINE OWNER
--
-- This is deliberately a composition/scope owner, not a replacement for the
-- empirical sciences and source traditions it coordinates.
------------------------------------------------------------------------

data AnthropologyBranch : Set where
  biologicalAnthropology : AnthropologyBranch
  socioculturalAnthropology : AnthropologyBranch
  linguisticAnthropology : AnthropologyBranch
  archaeologyHumanPast : AnthropologyBranch

record AnthropologyBranchStatus : Set where
  constructor anthropology-branch-status
  field
    branch : AnthropologyBranch
    reusableDashiSurface : String
    reusableSurfacePresent : Bool
    disciplineSpecificProducerPresent : Bool
    sourceLanePresent : Bool
open AnthropologyBranchStatus public

biologicalStatus : AnthropologyBranchStatus
biologicalStatus =
  anthropology-branch-status biologicalAnthropology
    "DASHI/Biology/* and human/person carriers"
    true false false

socioculturalStatus : AnthropologyBranchStatus
socioculturalStatus =
  anthropology-branch-status socioculturalAnthropology
    "DASHI/Culture/*; social cognition; Indigenous-knowledge and Mabo source-bounded fibres"
    true false true

linguisticStatus : AnthropologyBranchStatus
linguisticStatus =
  anthropology-branch-status linguisticAnthropology
    "DASHI/Culture/LinguisticAnthropologyTlureyPragmaticsBridgeExact.agda; Tlurey relational protocol; governed language-use machinery"
    true false true

archaeologyStatus : AnthropologyBranchStatus
archaeologyStatus =
  anthropology-branch-status archaeologyHumanPast
    "historical/provenance machinery exists, but proof-search uses of the word archaeology are not archaeology-the-discipline"
    true false false

record AnthropologyDisciplineOwner : Set where
  constructor anthropology-discipline-owner
  field
    externalConceptQid : String
    externalParentQid : String
    biological : AnthropologyBranchStatus
    sociocultural : AnthropologyBranchStatus
    linguistic : AnthropologyBranchStatus
    humanPast : AnthropologyBranchStatus
    ethnographicMethodContractPaid : Bool
    concreteEthnographicProducerPaid : Bool
    branchSpecificSourcesRemainIndependent : Bool
    wikipediaOrQidDefinesDiscipline : Bool
open AnthropologyDisciplineOwner public

canonicalAnthropologyDisciplineOwner : AnthropologyDisciplineOwner
canonicalAnthropologyDisciplineOwner =
  anthropology-discipline-owner
    "Q23404"
    "Q1156970"
    biologicalStatus
    socioculturalStatus
    linguisticStatus
    archaeologyStatus
    true
    false
    true
    false

------------------------------------------------------------------------
-- Remaining frontier after composition-owner payment.
------------------------------------------------------------------------

record AnthropologyProducerFrontier : Set where
  constructor anthropology-producer-frontier
  field
    biologicalProducer : Bool
    socioculturalProducer : Bool
    linguisticProducer : Bool
    humanPastProducer : Bool
    concreteFieldworkProducer : Bool
    architectureStillMissing : Bool
open AnthropologyProducerFrontier public

currentAnthropologyProducerFrontier : AnthropologyProducerFrontier
currentAnthropologyProducerFrontier =
  anthropology-producer-frontier false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CompositionOwnerCreatesEmpiricalAnthropology : Set where
data ExistingLanguageMachineryCreatesLinguisticAnthropology : Set where
data HistoricalProvenanceCreatesArchaeology : Set where

compositionOwnerIsNotEmpiricalAnthropology :
  CompositionOwnerCreatesEmpiricalAnthropology → ⊥
compositionOwnerIsNotEmpiricalAnthropology ()

languageMachineryIsNotLinguisticAnthropology :
  ExistingLanguageMachineryCreatesLinguisticAnthropology → ⊥
languageMachineryIsNotLinguisticAnthropology ()

historicalProvenanceIsNotArchaeology :
  HistoricalProvenanceCreatesArchaeology → ⊥
historicalProvenanceIsNotArchaeology ()
