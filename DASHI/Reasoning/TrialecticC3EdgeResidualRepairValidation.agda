module DASHI.Reasoning.TrialecticC3EdgeResidualRepairValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticC3EdgeResidualRepairExact as Repair

boundary : Repair.TrialecticC3EdgeResidualRepairBoundary
boundary = Repair.canonicalTrialecticC3EdgeResidualRepairBoundary

sameAWitnessForcesResidualSeparation :
  Repair.everySufficientResidualMustSeparateWitness boundary ≡ true
sameAWitnessForcesResidualSeparation = refl

selectedResidualReconstructsRotatedEdge :
  Repair.selectedResidualReconstructsWholeRotatedEdge boundary ≡ true
selectedResidualReconstructsRotatedEdge = refl

oldFullT9NotRequiredForThisConsumer :
  Repair.oldFullT9EdgeRequiredForRotatedEdgeConsumer boundary ≡ false
oldFullT9NotRequiredForThisConsumer = refl

residualMinimalityNotClaimed :
  Repair.selectedResidualClaimedMinimalUnique boundary ≡ false
residualMinimalityNotClaimed = refl
