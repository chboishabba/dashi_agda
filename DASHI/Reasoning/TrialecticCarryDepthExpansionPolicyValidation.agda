module DASHI.Reasoning.TrialecticCarryDepthExpansionPolicyValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticCarryDepthExpansionPolicyExact as Expansion

boundary : Expansion.TrialecticCarryDepthExpansionPolicyBoundary
boundary = Expansion.canonicalTrialecticCarryDepthExpansionPolicyBoundary

explicitExpansionPolicyPaid :
  Expansion.explicitExpansionPolicyConstructed boundary ≡ true
explicitExpansionPolicyPaid = refl

sameSeedHasDistinctBoundaryExpansions :
  Expansion.sameSeedDistinctBoundaryExpansionsPaid boundary ≡ true
sameSeedHasDistinctBoundaryExpansions = refl

sameBoundaryHasDistinctFaceExpansions :
  Expansion.sameBoundaryDistinctFaceExpansionsPaid boundary ≡ true
sameBoundaryHasDistinctFaceExpansions = refl

seedAloneDoesNotDetermineNextState :
  Expansion.carrySeedUniquelyDeterminesNextStructuredState boundary ≡ false
seedAloneDoesNotDetermineNextState = refl

allDepthCoherenceStillExplicit :
  Expansion.allDepthCoherenceAutomatic boundary ≡ false
allDepthCoherenceStillExplicit = refl
