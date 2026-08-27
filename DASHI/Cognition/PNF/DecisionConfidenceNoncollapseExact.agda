module DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence

------------------------------------------------------------------------
-- CONFIDENCE IS NOT IDENTICAL TO COMMITMENT
--
-- Literature calibration:
-- Roozbeh Kiani; Michael N. Shadlen,
-- "Representation of Confidence Associated with a Decision by Neurons in the
-- Parietal Cortex", DOI 10.1126/science.1169405.
--
-- The finite witness below only protects the type distinction.  It does not
-- claim a unique anatomical confidence decoder or that confidence is carried
-- exclusively by LIP.
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

record ConfidenceBoundary : Set where
  constructor confidenceBoundary
  field
    confidenceEqualsCommitment : Bool
    sameCommitmentForcesSameConfidence : Bool

canonicalConfidenceBoundary : ConfidenceBoundary
canonicalConfidenceBoundary = confidenceBoundary false false
