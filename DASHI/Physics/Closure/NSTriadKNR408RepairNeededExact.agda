module DASHI.Physics.Closure.NSTriadKNR408RepairNeededExact where

open import Agda.Builtin.Bool using (Bool; true)

-- Pending source repair: R408 uses propositional equality symmetry in rewrite.
-- Do not treat R408 as kernel-validated until the equality import is repaired
-- and an exact-head Agda build succeeds.
round408SourceRepairPending : Bool
round408SourceRepairPending = true
