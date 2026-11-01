module DASHI.ComputerScience.FlyEnvironmentalMultiStressorAdjacentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ADJACENT ENVIRONMENTAL MULTI-STRESSOR SOURCE
--
-- Luo et al. 2026 is retained because it is highly relevant to the generic
-- situated-observation architecture: the same Drosophila model and neural/
-- behavioural observers are used under a composite environmental exposure.
-- It is NOT a pesticide study and therefore cannot be used to pay a pesticide
-- mechanism or pesticide-mixture claim.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source =
  Attribution.mkDOISource
    "Luo, Zhang, Chen, Pan, Ding, Zhang, Li and Sun"
    "Nanoplastics exacerbate lead exposure-induced developmental neurotoxicity by disrupting gut integrity in Drosophila"
    "Neurotoxicology"
    "2026"
    "10.1016/j.neuro.2026.103407"
    "https://pubmed.ncbi.nlm.nih.gov/41692328/"
    Attribution.academicArticleSource
    "pays only the paper's Drosophila nanoplastic-plus-lead co-exposure observations and reported neural/gut/developmental readouts; it is adjacent environmental toxicology, not pesticide evidence"
    Attribution.publicAttribution

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleQid : Identity.ExternalIdentityDemand
articleQid =
  Identity.mkOptionalIdentityDemand
    "Fly environmental multi-stressor attribution"
    "Luo et al. 2026 article Wikidata identity"
    "Nanoplastics exacerbate lead exposure-induced developmental neurotoxicity by disrupting gut integrity in Drosophila"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID not independently verified")

drosophilaQid : Identity.ExternalIdentityDemand
drosophilaQid =
  Identity.mkOptionalIdentityDemand
    "Fly environmental multi-stressor attribution"
    "Drosophila melanogaster taxon identity"
    "Drosophila melanogaster"
    Identity.wikidataQid
    (Identity.verified "Wikidata" "Q130888")

data EnvironmentalExposureClass : Set where
  polystyreneNanoplasticExposure : EnvironmentalExposureClass
  leadExposure : EnvironmentalExposureClass
  nanoplasticLeadCoexposure : EnvironmentalExposureClass

data EnvironmentalObserver : Set where
  learningMemoryObserver
  climbingMotorObserver
  developmentObserver
  neuralAccumulationObserver
  oxidativeStressObserver
  neuromuscularJunctionObserver
  mushroomBodyGuidanceObserver
  gutIntegrityObserver : EnvironmentalObserver

record EnvironmentalMultiStressorObservation : Set where
  constructor environmental-multi-stressor-observation
  field
    exposureClass : EnvironmentalExposureClass
    observer : EnvironmentalObserver
    sourceLocator : String
    sourceBoundedReading : String
open EnvironmentalMultiStressorObservation public

coexposureMemoryObservation : EnvironmentalMultiStressorObservation
coexposureMemoryObservation = environmental-multi-stressor-observation
  nanoplasticLeadCoexposure
  learningMemoryObserver
  "Luo et al. 2026 abstract / behavioural tests"
  "source reports that nanoplastic-plus-lead co-exposure worsened learning/memory deficits compared with lead exposure alone"

coexposureNeuralAccumulationObservation : EnvironmentalMultiStressorObservation
coexposureNeuralAccumulationObservation = environmental-multi-stressor-observation
  nanoplasticLeadCoexposure
  neuralAccumulationObserver
  "Luo et al. 2026 abstract / mechanistic investigation"
  "source reports increased lead accumulation in neural tissues under co-exposure together with neural/gut/developmental effects"

------------------------------------------------------------------------
-- WrongType / adjacent-evidence firewalls.
------------------------------------------------------------------------

data EnvironmentalCoexposureIsPesticideEvidence : Set where
data SameEndpointImpliesSameExposureClass : Set where
data SameSpeciesImpliesSameMechanism : Set where
data CoexposureEffectCreatesUniversalSynergyLaw : Set where

environmentalCoexposureDoesNotBecomePesticideEvidence :
  EnvironmentalCoexposureIsPesticideEvidence → ⊥
environmentalCoexposureDoesNotBecomePesticideEvidence ()

sameEndpointDoesNotCreateSameExposureClass : SameEndpointImpliesSameExposureClass → ⊥
sameEndpointDoesNotCreateSameExposureClass ()

sameSpeciesDoesNotCreateSameMechanism : SameSpeciesImpliesSameMechanism → ⊥
sameSpeciesDoesNotCreateSameMechanism ()

coexposureEffectDoesNotCreateUniversalSynergyLaw :
  CoexposureEffectCreatesUniversalSynergyLaw → ⊥
coexposureEffectDoesNotCreateUniversalSynergyLaw ()

record FlyEnvironmentalMultiStressorBoundary : Set where
  constructor fly-environmental-multistressor-boundary
  field
    sameSpeciesAdjacentEvidenceRetained : Bool
    coexposureRoleRetained : Bool
    neuralBehaviourObserverOverlapRetained : Bool
    gutAndNeuralObserversKeptDistinct : Bool
    articleQidMayRemainUnresolved : Bool
    studyIsPesticideEvidence : Bool
    sameEndpointCreatesSameExposureClass : Bool
    sameSpeciesCreatesSameMechanism : Bool
    oneCoexposureCreatesUniversalSynergyLaw : Bool
open FlyEnvironmentalMultiStressorBoundary public

canonicalFlyEnvironmentalMultiStressorBoundary : FlyEnvironmentalMultiStressorBoundary
canonicalFlyEnvironmentalMultiStressorBoundary =
  fly-environmental-multistressor-boundary
    true true true true true
    false false false false
