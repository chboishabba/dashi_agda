module DASHI.Biology.KluverFormConstantPsychedelicBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.PsychedelicAttractorReweightingBoundary as Psychedelic

------------------------------------------------------------------------
-- KLÜVER FORM CONSTANTS x PSYCHEDELIC ATTRACTOR BOUNDARY
--
-- Source-bounded phenomenology: recurring geometric hallucination classes can
-- be described and related to candidate visual-cortical pattern-forming
-- mechanisms.  They are not a universal symbolic dictionary, proof of a
-- specific autobiographical memory, or authority to reinterpret Indigenous
-- cosmology/ceremonial meaning.
--
-- Source roles:
--   Heinrich Klüver: historical form-constant classification.
--   Bressloff et al., "What geometric visual hallucinations tell us about the
--   visual cortex", PMID 11860679: candidate cortical symmetry/pattern account.
------------------------------------------------------------------------

data FormConstant : Set where
  tunnelFunnel
  spiral
  latticeHoneycombTriangle
  cobweb
  : FormConstant

data PhenomenologyAuthority : Set where
  reportedPhenomenology
  neuralMechanismCandidate
  personalMeaningInterpretation
  culturalSymbolicInterpretation
  : PhenomenologyAuthority

record FormConstantObservation : Set where
  constructor formConstantObservation
  field
    form : FormConstant
    reportReference : String
    phenomenologyObserved : Bool
    fixedNeuralCauseProven : Bool
    fixedNeuralCauseProvenIsFalse : fixedNeuralCauseProven ≡ false
    universalMeaningProven : Bool
    universalMeaningProvenIsFalse : universalMeaningProven ≡ false

open FormConstantObservation public

canonicalLatticeObservation : FormConstantObservation
canonicalLatticeObservation = formConstantObservation
  latticeHoneycombTriangle
  "Klüver form-constant family; geometric visual pattern report"
  true
  false refl
  false refl

psychedelicBoundary : Psychedelic.PsychedelicAttractorBoundary
psychedelicBoundary = Psychedelic.canonicalPsychedelicAttractorBoundary

------------------------------------------------------------------------
-- Shape recurrence can constrain mechanism hypotheses while leaving personal,
-- cultural and symbolic meaning open.
------------------------------------------------------------------------

data FormConstantPromotesUniversalSymbol : Set where

data FormConstantPromotesRecoveredMemory : Set where

data CorticalModelPromotesCompleteExperienceMeaning : Set where

formConstantDoesNotPromoteUniversalSymbol :
  FormConstantPromotesUniversalSymbol → ⊥
formConstantDoesNotPromoteUniversalSymbol ()

formConstantDoesNotPromoteRecoveredMemory :
  FormConstantPromotesRecoveredMemory → ⊥
formConstantDoesNotPromoteRecoveredMemory ()

corticalModelDoesNotPromoteCompleteMeaning :
  CorticalModelPromotesCompleteExperienceMeaning → ⊥
corticalModelDoesNotPromoteCompleteMeaning ()

record KluverPsychedelicBoundary : Set where
  constructor kluverPsychedelicBoundary
  field
    recurrentGeometryCanBePhenomenologicallyTyped : Bool
    recurrentGeometryCanBePhenomenologicallyTypedIsTrue :
      recurrentGeometryCanBePhenomenologicallyTyped ≡ true
    visualCorticalPatterningIsCandidateMechanism : Bool
    visualCorticalPatterningIsCandidateMechanismIsTrue :
      visualCorticalPatterningIsCandidateMechanism ≡ true
    recurrentGeometryEqualsUniversalSymbolDictionary : Bool
    recurrentGeometryEqualsUniversalSymbolDictionaryIsFalse :
      recurrentGeometryEqualsUniversalSymbolDictionary ≡ false
    psychedelicVisionProvesRecoveredMemory : Bool
    psychedelicVisionProvesRecoveredMemoryIsFalse :
      psychedelicVisionProvesRecoveredMemory ≡ false
    neuralRegularityTransfersCulturalInterpretiveAuthority : Bool
    neuralRegularityTransfersCulturalInterpretiveAuthorityIsFalse :
      neuralRegularityTransfersCulturalInterpretiveAuthority ≡ false

canonicalKluverPsychedelicBoundary : KluverPsychedelicBoundary
canonicalKluverPsychedelicBoundary =
  kluverPsychedelicBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
