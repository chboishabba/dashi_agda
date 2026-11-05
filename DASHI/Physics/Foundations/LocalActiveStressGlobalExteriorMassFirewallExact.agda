{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.LocalActiveStressGlobalExteriorMassFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Local
import DASHI.Physics.Foundations.PositiveGAnisotropicTOVConservationExact as TOV

------------------------------------------------------------------------
-- LOCAL ACTIVE-STRESS SIGN != GLOBAL EXTERIOR-MASS SIGN
--
-- A local negative value of rho + p_r + 2 p_t is a focusing/defocusing source
-- diagnostic.  It is not definitionally an ADM/Komar mass calculation and does
-- not by itself construct an asymptotically-flat repulsive exterior solution.
-- Conservation, junction/matching conditions and the global mass charge must be
-- solved on the same stress tensor before that promotion is allowed.
------------------------------------------------------------------------

data LocalNegativeActiveStressAutomaticallyGivesNegativeGlobalMass : Set where
data LocalOutwardToyResponseAutomaticallyIsExactGRExterior : Set where

localActiveStressDoesNotAutomaticallyGiveNegativeGlobalMass :
  LocalNegativeActiveStressAutomaticallyGivesNegativeGlobalMass → ⊥
localActiveStressDoesNotAutomaticallyGiveNegativeGlobalMass ()

localToyResponseIsNotAutomaticallyExactGRExterior :
  LocalOutwardToyResponseAutomaticallyIsExactGRExterior → ⊥
localToyResponseIsNotAutomaticallyExactGRExterior ()

existingLocalShell : Local.LocalizedAnisotropicRepulsiveShellWitness
existingLocalShell = Local.canonicalLocalizedAnisotropicRepulsiveShellWitness

existingConservationAudit : TOV.AnisotropicTOVConservationBoundary
existingConservationAudit = TOV.canonicalAnisotropicTOVConservationBoundary

record LocalGlobalExteriorBoundary : Set where
  constructor local-global-exterior-boundary
  field
    localActiveStressSignKnown : Bool
    localActiveStressFixesGlobalMassSign : Bool
    currentTwoZoneFixtureConservationClosed : Bool
    exactJunctionConditionsSolved : Bool
    exactGlobalExteriorMassChargeSolved : Bool
    exactAsymptoticallyFlatExteriorMetricSolved : Bool
    globalExteriorPromotionRequiresAllThoseReceipts : Bool

canonicalLocalGlobalExteriorBoundary : LocalGlobalExteriorBoundary
canonicalLocalGlobalExteriorBoundary =
  local-global-exterior-boundary
    true false false false false false true
