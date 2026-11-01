module DASHI.Core.FragmentationCompositionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FragmentationCompositionExact as Frag

narrative-coherence-cannot-answer-event-truth :
  Frag.EventTruthQueryAdequate → ⊥
narrative-coherence-cannot-answer-event-truth =
  Frag.eventTruthNotAdequate

local-intelligibility-cannot-answer-global-defensibility :
  Frag.GlobalDefensibilityQueryAdequate → ⊥
local-intelligibility-cannot-answer-global-defensibility =
  Frag.globalDefensibilityNotAdequate

fragmentation-does-not-prove-trauma :
  Frag.fragmentedNarrativeAutomaticallyEstablishesTrauma
    Frag.canonicalFragmentationBoundary ≡ false
fragmentation-does-not-prove-trauma = refl

local-role-compliance-does-not-pay-global-justification :
  Frag.localRoleComplianceAutomaticallyGlobalJustification
    Frag.canonicalFragmentationBoundary ≡ false
local-role-compliance-does-not-pay-global-justification = refl
