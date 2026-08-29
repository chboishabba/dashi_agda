module DASHI.Physics.Closure.NSTriadKNSmallDataVsArbitraryFrontierRound182Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Round182: fail-closed separation of the Lean small-data closure from the
-- arbitrary-data Clay package.
------------------------------------------------------------------------

data CriticalRegime : Set where
  belowExplicitThreshold : CriticalRegime
  arbitraryCriticalData  : CriticalRegime

record ClosureStatus : Set where
  constructor status
  field
    companionBudgetClosed : Bool
    arbitraryPackageAClosed : Bool

smallDataStatus : ClosureStatus
smallDataStatus = status true false

arbitraryDataStatus : ClosureStatus
arbitraryDataStatus = status false false

small-data-does-not-promote-A :
  ClosureStatus.arbitraryPackageAClosed smallDataStatus ≡ false
small-data-does-not-promote-A = refl

-- This module is intentionally tiny: its role is regression safety.  A later
-- arbitrary-data theorem must replace `arbitraryDataStatus`; the existing
-- small-data result can never silently flip the Clay-facing bit.
