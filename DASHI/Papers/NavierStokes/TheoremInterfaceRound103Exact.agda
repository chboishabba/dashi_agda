module DASHI.Papers.NavierStokes.TheoremInterfaceRound103Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND103 STATUS
--
-- The current shortest path remains two theorem-sized obligations at the
-- physical level, but the standard compactness/continuation composition is now
-- represented by a theorem-bearing same-solution compiler rather than a loose
-- status receipt.
--
-- New mathematical narrowing:
--
--   conservative radial transfer does not vanish after derivative weighting;
--   it obeys a discrete integration-by-parts identity.  A down-gradient edge
--   law would make the whole weighted transfer a negative Dirichlet form.
--
-- The unresolved frontier is therefore the physical theorem identifying the
-- literal heterochiral Waleffe/minority-leg transfer with such a signed summed
-- mechanism (or something stronger) strongly enough to build the arbitrary-
-- data cutoff-uniform H^(1/2)/H^(3/2) barrier.
--
-- The standard Simon/Aubin--Lions realization on the literal Galerkin family
-- remains open; once supplied, the Round103 compiler produces the exact
-- Round90 CriticalBarrierFor for the same limiting solution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound103Exact as R103

round103PaperRadialFluxIBPClosed : Bool
round103PaperRadialFluxIBPClosed =
  R103.round103RadialFluxIntegrationByPartsClosed

round103PaperSameSolutionLimitCompilerClosed : Bool
round103PaperSameSolutionLimitCompilerClosed =
  R103.round103SameSolutionCriticalPassageCompilerClosed

round103PaperUniformGalerkinCriticalBarrierClosed : Bool
round103PaperUniformGalerkinCriticalBarrierClosed =
  R103.round103UniformGalerkinCriticalBarrierClosed

round103PaperPhysicalSimonInstantiationClosed : Bool
round103PaperPhysicalSimonInstantiationClosed =
  R103.round103PhysicalSimonAubinLionsInstantiationClosed

round103PaperRadialFluxIBPClosedIsTrue :
  round103PaperRadialFluxIBPClosed ≡ true
round103PaperRadialFluxIBPClosedIsTrue = refl

round103PaperSameSolutionLimitCompilerClosedIsTrue :
  round103PaperSameSolutionLimitCompilerClosed ≡ true
round103PaperSameSolutionLimitCompilerClosedIsTrue = refl

round103PaperUniformGalerkinCriticalBarrierClosedIsFalse :
  round103PaperUniformGalerkinCriticalBarrierClosed ≡ false
round103PaperUniformGalerkinCriticalBarrierClosedIsFalse = refl

round103PaperPhysicalSimonInstantiationClosedIsFalse :
  round103PaperPhysicalSimonInstantiationClosed ≡ false
round103PaperPhysicalSimonInstantiationClosedIsFalse = refl

round103PaperClayPromotion : Bool
round103PaperClayPromotion = false

round103PaperClayPromotionIsFalse : round103PaperClayPromotion ≡ false
round103PaperClayPromotionIsFalse = refl
