module DASHI.Law.TraumaNarrativeEvidenceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.FragmentationCompositionExact as Fragmentation

------------------------------------------------------------------------
-- TRAUMA NARRATIVE EVIDENCE BOUNDARY
--
-- Empirical source layer for the generic fragmentation theorem.  The reviews
-- support a cautious boundary: trauma/PTSD narrative fragmentation is an
-- empirical question with heterogeneous/inconclusive findings, not a truth,
-- falsity or diagnosis primitive.
------------------------------------------------------------------------

okearneyPerrott2006 : Source.AttributedSource
okearneyPerrott2006 = Source.mkDOISource
  "Richard O'Kearney and Kelly Perrott"
  "Trauma narratives in posttraumatic stress disorder: a review"
  "Journal of Traumatic Stress 19(1):81-93"
  "2006"
  "10.1002/jts.20099"
  "https://pubmed.ncbi.nlm.nih.gov/16568467/"
  Source.academicArticleSource
  "Review of 19 empirical studies. Reports evidence for some sensory/perceptual and temporal features while finding evidence for PTSD-related narrative fragmentation inconclusive and noting validity/measurement limitations. Does not diagnose or determine truth in an individual case."
  Source.publicAttribution

crespoFernandezLansac2016 : Source.AttributedSource
crespoFernandezLansac2016 = Source.mkDOISource
  "María Crespo and Violeta Fernández-Lansac"
  "Memory and narrative of traumatic events: A literature review"
  "Psychological Trauma: Theory, Research, Practice, and Policy 8(2):149-156"
  "2016"
  "10.1037/tra0000041"
  "https://pubmed.ncbi.nlm.nih.gov/25915647/"
  Source.academicArticleSource
  "Review of 22 studies reporting sensory/perceptual and emotional features while describing results on fragmentation, length, temporal context and self-reference as heterogeneous. Does not supply a universal trauma-narrative signature."
  Source.publicAttribution

traumaNarrativeEvidenceSources : List Source.AttributedSource
traumaNarrativeEvidenceSources =
  okearneyPerrott2006 ∷ crespoFernandezLansac2016 ∷ []

traumaNarrativeEvidenceAtlas : Source.AttributedSourceAtlas
traumaNarrativeEvidenceAtlas = Source.mkSourceAtlas
  "trauma narrative evidence source atlas"
  "DASHI.Law.TraumaNarrativeEvidenceBoundaryExact"
  traumaNarrativeEvidenceSources
  "Review evidence concerning trauma/PTSD narratives. Fragmentation, coherence, diagnosis, memory accuracy and event truth remain separate coordinates."

parentFragmentationBoundary : Fragmentation.FragmentationBoundary
parentFragmentationBoundary = Fragmentation.canonicalFragmentationBoundary

record TraumaNarrativeEvidenceBoundary : Set where
  constructor traumaNarrativeEvidenceBoundary
  field
    parentFragmentationReused : Bool
    reviewEvidenceForPTSDNarrativeFragmentationInconclusive : Bool
    laterReviewNarrativeFragmentationResultsHeterogeneous : Bool
    traumaAutomaticallyFragmentedNarrative : Bool
    fragmentedNarrativeAutomaticallyTrauma : Bool
    fragmentedNarrativeAutomaticallyPTSD : Bool
    narrativeCoherenceAutomaticallyTruth : Bool
    narrativeFragmentationAutomaticallyFalsity : Bool
    traumaMemoryAutomaticallyAccurate : Bool
    traumaMemoryAutomaticallyInaccurate : Bool
    reviewScholarshipAutomaticallyCaseSpecificFinding : Bool

open TraumaNarrativeEvidenceBoundary public

canonicalTraumaNarrativeEvidenceBoundary : TraumaNarrativeEvidenceBoundary
canonicalTraumaNarrativeEvidenceBoundary =
  traumaNarrativeEvidenceBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false

data FragmentedNarrativeEstablishesTrauma : Set where
data CoherentNarrativeEstablishesTruth : Set where
data FragmentedNarrativeEstablishesFalsity : Set where

fragmentedNarrativeDoesNotEstablishTrauma :
  FragmentedNarrativeEstablishesTrauma → ⊥
fragmentedNarrativeDoesNotEstablishTrauma ()

coherentNarrativeDoesNotEstablishTruth :
  CoherentNarrativeEstablishesTruth → ⊥
coherentNarrativeDoesNotEstablishTruth ()

fragmentedNarrativeDoesNotEstablishFalsity :
  FragmentedNarrativeEstablishesFalsity → ⊥
fragmentedNarrativeDoesNotEstablishFalsity ()
