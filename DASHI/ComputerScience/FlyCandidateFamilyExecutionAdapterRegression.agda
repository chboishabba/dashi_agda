module DASHI.ComputerScience.FlyCandidateFamilyExecutionAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CandidateFamilyExecutionExact as Family
import DASHI.ComputerScience.FlyCandidateFamilyExecutionAdapterExact as Adapter

flyFamilySpine : Family.CandidateFamilyExecutionSpine
flyFamilySpine = Adapter.flyCandidateFamilyExecutionSpine

heldOutSuccessClaimed : Bool
heldOutSuccessClaimed =
  Adapter.FlyCandidateFamilyExecutionBoundary.globalCompositionPromotedToHeldOutSuccess
    Adapter.canonicalFlyCandidateFamilyExecutionBoundary

heldOutSuccessClaimedIsFalse : heldOutSuccessClaimed ≡ false
heldOutSuccessClaimedIsFalse = refl
