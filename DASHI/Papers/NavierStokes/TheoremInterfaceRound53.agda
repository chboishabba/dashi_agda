module DASHI.Papers.NavierStokes.TheoremInterfaceRound53 where

------------------------------------------------------------------------
-- Paper-facing Round-53 extension.
--
-- Keep the established theorem/status interface untouched and import the new
-- highest-alpha aggregate alongside it.  This is intentionally non-promoting:
-- all existing Clay/terminal false proofs remain inherited from
-- TheoremInterface, while Round 53's exact physical-producer theorem surfaces
-- become reachable from a paper module without inventing new status booleans.
------------------------------------------------------------------------

open import DASHI.Papers.NavierStokes.TheoremInterface public
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound53Exact
