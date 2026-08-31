module DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence

------------------------------------------------------------------------
-- CONFIDENCE IS NOT IDENTICAL TO COMMITMENT OR EVIDENCE HISTORY
--
-- Literature calibration:
-- Roozbeh Kiani; Michael N. Shadlen,
-- "Representation of Confidence Associated with a Decision by Neurons in the
-- Parietal Cortex", DOI 10.1126/science.1169405.
--
-- Michael Pereira; Nathan Faivre; Iñaki Iturrate; Marco Wirthlin; Luana
-- Serafini; Stephanie Martin; Arnaud Desvachez; Olaf Blanke; Dimitri Van De
-- Ville; José del R. Millán,
-- "Disentangling the origins of confidence in speeded perceptual judgments
-- through multimodal imaging", DOI 10.1073/pnas.1918335117.
------------------------------------------------------------------------

data Confidence : Set where lowConfidence highConfidence : Confidence

record DecisionReadout : Set where
  constructor decisionReadout
  field
    commitment : Evidence.ThresholdCommitment
    confidence : Confidence

open DecisionReadout public

committedLowConfidence : DecisionReadout
committedLowConfidence = decisionReadout Evidence.committed lowConfidence

committedHighConfidence : DecisionReadout
committedHighConfidence = decisionReadout Evidence.committed highConfidence

sameCommitmentDifferentConfidence :
  commitment committedLowConfidence ≡ commitment committedHighConfidence
sameCommitmentDifferentConfidence = refl

commitmentDoesNotDetermineConfidence :
  committedLowConfidence ≡ committedHighConfidence → ⊥
commitmentDoesNotDetermineConfidence ()

record ConfidenceHistoryReadout : Set where
  constructor confidenceHistoryReadout
  field
    evidenceHistory : Evidence.EvidenceLevel
    historyConfidence : Confidence

open ConfidenceHistoryReadout public

highConfidenceAfterOne : ConfidenceHistoryReadout
highConfidenceAfterOne = confidenceHistoryReadout Evidence.e1 highConfidence

highConfidenceAfterTwo : ConfidenceHistoryReadout
highConfidenceAfterTwo = confidenceHistoryReadout Evidence.e2 highConfidence

sameConfidenceDifferentEvidenceHistory :
  historyConfidence highConfidenceAfterOne
  ≡ historyConfidence highConfidenceAfterTwo
  × (evidenceHistory highConfidenceAfterOne
      ≡ evidenceHistory highConfidenceAfterTwo → ⊥)
sameConfidenceDifferentEvidenceHistory = refl , (λ ())

confidenceCannotRecoverEvidenceHistory :
  NF.FactorsThrough historyConfidence evidenceHistory → ⊥
confidenceCannotRecoverEvidenceHistory =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      highConfidenceAfterOne highConfidenceAfterTwo refl (λ ()))

record ConfidenceBoundary : Set where
  constructor confidenceBoundary
  field
    confidenceEqualsCommitment : Bool
    sameCommitmentForcesSameConfidence : Bool
    sameConfidenceForcesSameEvidenceHistory : Bool
    postdecisionalConfidenceSeparatelyRepresentable : Bool

canonicalConfidenceBoundary : ConfidenceBoundary
canonicalConfidenceBoundary = confidenceBoundary false false false true
