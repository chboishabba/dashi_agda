module DASHI.Law.AustralianNeurodiversityWitnessCredibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as SituatedExpert
import DASHI.Law.AustralianDisabilityJusticeObserverFixtureExact as Disability

------------------------------------------------------------------------
-- AUSTRALIAN NEURODIVERSITY / WITNESS-CREDIBILITY FIXTURE
--
-- Pays the autism/neurodiversity-specific empirical dependency that the broader
-- disability fixture deliberately left open.  It does not diagnose any person,
-- make neurodivergence a credibility class, or promote mock-juror/survey effects
-- into universal court behaviour.
------------------------------------------------------------------------

bozinaEtAl2026 : Source.AttributedSource
bozinaEtAl2026 = Source.mkDOISource
  "Danielle Bozina, Vincent Denault, Karen A. Sullivan, Catherine Kennon, Lucy Cradduck and Rachel Hews"
  "Understanding the impact of neurodiversity on witness credibility assessment in Courts, Tribunals and Commissions"
  "Psychiatry, Psychology and Law"
  "2026"
  "10.1080/13218719.2026.2663445"
  "https://www.tandfonline.com/doi/full/10.1080/13218719.2026.2663445"
  Source.academicArticleSource
  "Australian cross-sectional survey of 23 Queensland judicial and quasi-judicial officers concerning neurodivergent witness credibility/reliability assessment. Supports a bounded risk proposition that visible neuroatypical characteristics may be negatively perceived and that some erroneous beliefs were present; does not establish bias by any named judicial officer or every court."
  Source.publicAttribution

smithVanGoldeAutisticWitness : Source.AttributedSource
smithVanGoldeAutisticWitness = Source.mkDOISource
  "Joshua W. S. Smith and Celine van Golde"
  "Mock juror perceptions of an adult autistic witness: effect of diagnostic label and witness intermediary presence"
  "Psychiatry, Psychology and Law 33(2):295-318"
  "2026"
  "10.1080/13218719.2024.2404856"
  "https://pubmed.ncbi.nlm.nih.gov/41859277/"
  Source.academicArticleSource
  "Australian mock-juror study of an adult autistic witness. The reported experiment found perception changes associated with diagnostic information and suggested misattribution of autism-related behaviour to nervousness in its design. Mock-juror results do not automatically generalise to real courts, all autistic witnesses, or truth of testimony."
  Source.publicAttribution

australianNeurodiversityWitnessSources : List Source.AttributedSource
australianNeurodiversityWitnessSources =
  bozinaEtAl2026 ∷ smithVanGoldeAutisticWitness ∷ []

australianNeurodiversityWitnessAtlas : Source.AttributedSourceAtlas
australianNeurodiversityWitnessAtlas = Source.mkSourceAtlas
  "Australian neurodiversity witness credibility source atlas"
  "DASHI.Law.AustralianNeurodiversityWitnessCredibilityExact"
  australianNeurodiversityWitnessSources
  "Neurodiversity-specific Australian judicial survey plus autism-specific mock-witness experiment. Behavioural presentation, diagnostic status, credibility, reliability and truth remain separate coordinates."

parentSituatedExpertBoundary : SituatedExpert.ExpertSituatedObserverBoundary
parentSituatedExpertBoundary = SituatedExpert.canonicalExpertSituatedObserverBoundary

parentDisabilityJusticeBoundary : Disability.AustralianDisabilityJusticeObserverBoundary
parentDisabilityJusticeBoundary = Disability.canonicalAustralianDisabilityJusticeObserverBoundary

record AustralianNeurodiversityWitnessBoundary : Set where
  constructor australianNeurodiversityWitnessBoundary
  field
    parentSituatedObserverReused : Bool
    parentDisabilityJusticeReused : Bool
    queenslandJudicialNeurodiversityStudyPaid : Bool
    autisticAdultMockWitnessStudyPaid : Bool
    visibleNeuroatypicalCharacteristicsMayBeNegativelyPerceivedPaid : Bool
    neurodivergenceAutomaticallyUnreliable : Bool
    atypicalAffectAutomaticallyDishonest : Bool
    eyeContactDifferenceAutomaticallyEvasive : Bool
    diagnosticLabelAutomaticallyTruthOrCredibilityAuthority : Bool
    mockJurorEffectAutomaticallyRealCourtEffect : Bool
    oneAutismStudyAutomaticallyAllNeurodivergence : Bool
    sourceScholarshipAutomaticallyDiagnosesObservedPerson : Bool
    accommodationAutomaticallyEstablishesTruth : Bool

open AustralianNeurodiversityWitnessBoundary public

canonicalAustralianNeurodiversityWitnessBoundary :
  AustralianNeurodiversityWitnessBoundary
canonicalAustralianNeurodiversityWitnessBoundary =
  australianNeurodiversityWitnessBoundary
    true
    true
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

data NeurodivergenceEstablishesUnreliability : Set where
data DiagnosticLabelEstablishesTruth : Set where
data MockJurorEffectEstablishesRealCourtEffect : Set where

neurodivergenceDoesNotEstablishUnreliability :
  NeurodivergenceEstablishesUnreliability → ⊥
neurodivergenceDoesNotEstablishUnreliability ()

diagnosticLabelDoesNotEstablishTruth : DiagnosticLabelEstablishesTruth → ⊥
diagnosticLabelDoesNotEstablishTruth ()

mockJurorEffectDoesNotEstablishRealCourtEffect :
  MockJurorEffectEstablishesRealCourtEffect → ⊥
mockJurorEffectDoesNotEstablishRealCourtEffect ()
