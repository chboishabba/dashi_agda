module DASHI.Unified.ResearchCapsuleNonPromotionExact where

-- PNF research verbs are instructions, not mathematical evidence.
-- Reuse existing proxy and empirical boundaries without promoting them.
-- The original owners retain attribution in their imported modules.

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.GluingOperatorLinearityProxyHarnessResult as Gluing
import DASHI.Physics.Closure.YMFiniteSelfAdjointHamiltonianProxyHarnessResult as Finite
import DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult as Domination
import DASHI.Biology.Levin.FungalNetworkAgencyBoundary as Fungal

gluingProxyDoesNotPromote :
  Gluing.terminalPromotion ≡ false
gluingProxyDoesNotPromote =
  Gluing.canonicalGluingHarnessTerminalPromotionFalse

finiteHamiltonianProxyDoesNotPromote :
  Finite.terminalPromotionField
    Finite.canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult ≡ false
finiteHamiltonianProxyDoesNotPromote =
  Finite.canonicalHarnessTerminalPromotionFalse

dominationProxyDoesNotPromote :
  Domination.terminalPromotionField
    Domination.canonicalYMHamiltonianDominationProxyHarnessResult ≡ false
dominationProxyDoesNotPromote =
  Domination.canonicalHamiltonianDominationProxyTerminalFalse

fungalNetworkNeedsSpeciesEvidence :
  Fungal.FungalNetworkAgencyBoundary.forestWideWoodWebClaimsNeedSpeciesSpecificEvidence
    Fungal.canonicalFungalNetworkAgencyBoundary ≡ true
fungalNetworkNeedsSpeciesEvidence = refl

noGluingProxyTerminalPromotion :
  Gluing.terminalPromotion ≡ true → ⊥
noGluingProxyTerminalPromotion =
  Gluing.noTerminalPromotionFromGluingProxyHarnessAlone
