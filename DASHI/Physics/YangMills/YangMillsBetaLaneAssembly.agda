module DASHI.Physics.YangMills.YangMillsBetaLaneAssembly where

-- A narrow assembly surface containing proof terms only.  This module does not
-- assert analytic inputs, source authority, or Clay promotion.

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( BalabanBetaPrefixBound
  ; InverseSquareThresholdControlsCoupling
  )
open import DASHI.Physics.YangMills.BalabanEndpointDeterminantPrefixBridge using
  ( EndpointDeterminantPrefixData
  ; endpointDeterminantToBetaPrefix
  )

record YangMillsBetaLaneAssembly : Set₁ where
  field
    prefixComposition :
      (K : Nat) →
      (step : BalabanInverseSquareCouplingStep) →
      (prefixData : EndpointDeterminantPrefixData K step) →
      {γ : _} →
      (threshold : InverseSquareThresholdControlsCoupling K γ step) →
      -- The remaining arguments are exactly those required by the existing
      -- composition theorem.  They stay explicit inputs rather than statuses.
      Set

-- The actual theorem remains the canonical implementation consumed by atlas
-- generation.  This alias prevents a second handwritten proof-status surface.
betaLanePrefixComposition = endpointDeterminantToBetaPrefix
