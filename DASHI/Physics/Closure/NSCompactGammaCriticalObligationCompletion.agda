module DASHI.Physics.Closure.NSCompactGammaCriticalObligationCompletion where

------------------------------------------------------------------------
-- Compatibility surface.
--
-- The previous version encoded shell propagation with the additive recurrence
--
--   C (n + 1) = step + C n,
--
-- which cannot prove geometric decay.  The authoritative completion now uses
-- the multiplicative recurrence a(n+1) <= rho*a(n)+r(n), rho<1, and exports the
-- complete SD/GM/parameter/coverage/real-analysis/Galerkin/off-packet/Bernstein
-- cutset from one fail-closed owner.
------------------------------------------------------------------------

open import DASHI.Physics.Closure.NSCompactGammaExactMathematicalCutset public
