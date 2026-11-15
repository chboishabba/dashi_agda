module DASHI.Reasoning.TrialecticT27WavePhaseHigherStackValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT27WavePhaseHigherStackExact as Higher27

boundary : Higher27.TrialecticT27WavePhaseHigherStackBoundary
boundary = Higher27.canonicalTrialecticT27WavePhaseHigherStackBoundary

groupoidPaid : Higher27.completedT27GroupoidPresheafPaid boundary ≡ true
groupoidPaid = refl

pseudofunctorPaid : Higher27.completedT27RestrictionPseudofunctorPaid boundary ≡ true
pseudofunctorPaid = refl

effectiveStackPaid : Higher27.completedT27EffectiveStackPaid boundary ≡ true
effectiveStackPaid = refl

twoCellPaid : Higher27.completedT27TwoCellCalculusPaid boundary ≡ true
twoCellPaid = refl

higherStackPaid : Higher27.certifiedCompletedT27HigherStack boundary ≡ true
higherStackPaid = refl

finiteHypersheafPaid : Higher27.certifiedCompletedT27FiniteHypersheaf boundary ≡ true
finiteHypersheafPaid = refl

ambientNotPromoted : Higher27.unconstrainedAmbientT27HigherStackClaimed boundary ≡ false
ambientNotPromoted = refl

arbitraryInfinityStillSeparate : Higher27.certifiedArbitraryInfinityT27Hypersheaf boundary ≡ false
arbitraryInfinityStillSeparate = refl
