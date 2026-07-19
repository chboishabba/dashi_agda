module DASHI.Physics.Closure.NSCompactGammaUniformFamilyResidence where

open import Agda.Primitive using (Set; Set₁)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Cutoff/shell/state-uniform residence reduction.
--
-- The preceding compact-Gamma absorption theorem is pointwise in one packet
-- and one interval.  This module records the exact additional structure needed
-- to make the resulting bound uniform over a declared family of cutoffs,
-- shells, and states.
--
-- No analytic estimate is manufactured here.  In particular, constructing
-- `memberUpperBound` with one cutoff/shell-independent scalar remains the
-- continuum analysis obligation.
------------------------------------------------------------------------

record CompactGammaCutoffShellFamily
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Cutoff : Set
    Shell : Set
    State : Set

    member :
      Cutoff → Shell → State →
      CompactGammaAbsorbedResidenceInputs A

    uniformUpper : Scalar A

    memberUpperBound :
      (cutoff : Cutoff) →
      (shell : Shell) →
      (state : State) →
      _≤_ A
        (_+_ A
          (initialPotential
            (absorptionInputs (member cutoff shell state)))
          (remainderConstant
            (absorptionInputs (member cutoff shell state))))
        uniformUpper

open CompactGammaCutoffShellFamily public

uniformCompactGammaResidenceBound :
  (A : AbsorptionArithmetic) →
  (F : CompactGammaCutoffShellFamily A) →
  (cutoff : Cutoff F) →
  (shell : Shell F) →
  (state : State F) →
  _≤_ A
    (dangerousResidenceExpenditure (member F cutoff shell state))
    (uniformUpper F)
uniformCompactGammaResidenceBound A F cutoff shell state =
  ≤-trans A
    (absorbedCompactGammaReplenishmentBoundsResidence A
      (member F cutoff shell state))
    (memberUpperBound F cutoff shell state)

------------------------------------------------------------------------
-- A reusable theorem socket matching the empirical audit vocabulary.
--
-- `sampledTheta` and `sampledCLambda` are deliberately not fields here:
-- numerical extrema do not construct analytic inequalities.  A future proof
-- must first package its actual danger-to-margin and replenishment estimates
-- into `CompactGammaAbsorbedResidenceInputs`, and then prove one common upper
-- bound through `memberUpperBound`.
------------------------------------------------------------------------

record CompactGammaUniformityReceipt
    (A : AbsorptionArithmetic) : Set₁ where
  field
    family : CompactGammaCutoffShellFamily A

    finiteGalerkinEvidenceOnly : Set
    cutoffUniformEstimateProved : Set
    continuumCompactnessProved : Set
    bkmBridgeProved : Set
    clayPromotionProved : Set

open CompactGammaUniformityReceipt public
