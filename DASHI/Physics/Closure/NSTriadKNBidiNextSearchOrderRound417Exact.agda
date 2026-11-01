module DASHI.Physics.Closure.NSTriadKNBidiNextSearchOrderRound417Exact where

open import Agda.Builtin.Bool using (Bool; true; false)

-- Search order: first try to derive the R409 scalar derivative from existing
-- derivative closure laws; in parallel search backward from the critical
-- continuation consumer for a phase-sensitive estimate that can also pay R410.
round417SearchDerivativeClosureFirst : Bool
round417SearchDerivativeClosureFirst = true

round417SearchDualSignedCriticalEstimateInParallel : Bool
round417SearchDualSignedCriticalEstimateInParallel = true

round417PolishFTCBeforeCancellation : Bool
round417PolishFTCBeforeCancellation = false
