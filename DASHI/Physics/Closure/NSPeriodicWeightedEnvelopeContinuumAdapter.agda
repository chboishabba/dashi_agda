module DASHI.Physics.Closure.NSPeriodicWeightedEnvelopeContinuumAdapter where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicWeightedEnvelopeLimitTransport as Weighted
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Carrier-coherent adapter from weighted-envelope transport to the continuum
-- vorticity premise used by the final BKM package.
------------------------------------------------------------------------

record PeriodicWeightedEnvelopeContinuumInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (InitialDatum ContinuumSolution Time Family Subsequence : Set i) :
    Set (lsuc i) where
  field
    SmoothDivergenceFreeMeanZero : InitialDatum → Set i
    CutoffUniformBound : InitialDatum → Family → Time → Set i

    limitSolution :
      InitialDatum → Family → Subsequence → ContinuumSolution

    ContinuumVorticityIntegralFinite :
      ContinuumSolution → Time → Set i

    weightedLimitInputs :
      ∀ u₀ T family subsequence →
      SmoothDivergenceFreeMeanZero u₀ →
      CutoffUniformBound u₀ family T →
      Weighted.PeriodicWeightedEnvelopeLimitInputs A

    weightedFiniteMeansContinuumFinite :
      ∀ u₀ T family subsequence
        (smooth : SmoothDivergenceFreeMeanZero u₀)
        (uniform : CutoffUniformBound u₀ family T) →
      Weighted.ContinuumVorticityExpenditureFinite
        (weightedLimitInputs u₀ T family subsequence smooth uniform) →
      ContinuumVorticityIntegralFinite
        (limitSolution u₀ family subsequence) T

open PeriodicWeightedEnvelopeContinuumInputs public

weightedEnvelopeVorticityBoundPassesToLimit :
  ∀ {i} {A : AbsorptionArithmetic}
    {InitialDatum ContinuumSolution Time Family Subsequence : Set i} →
  (C : PeriodicWeightedEnvelopeContinuumInputs
    A InitialDatum ContinuumSolution Time Family Subsequence) →
  ∀ u₀ T family subsequence →
  SmoothDivergenceFreeMeanZero C u₀ →
  CutoffUniformBound C u₀ family T →
  ContinuumVorticityIntegralFinite C
    (limitSolution C u₀ family subsequence) T
weightedEnvelopeVorticityBoundPassesToLimit
    C u₀ T family subsequence smooth uniform =
  weightedFiniteMeansContinuumFinite C
    u₀ T family subsequence smooth uniform
    (Weighted.weightedEnvelopeTransportGivesFiniteContinuumVorticity
      (weightedLimitInputs C u₀ T family subsequence smooth uniform))

------------------------------------------------------------------------
-- Status: the final continuum premise is now obtained from fixed-shell,
-- finite-partial, and least-upper-bound weighted-envelope transport rather
-- than from an opaque direct L1_t L-infinity_x limit assertion.
------------------------------------------------------------------------

weightedEnvelopeContinuumAdapterLevel : ProofLevel
weightedEnvelopeContinuumAdapterLevel = machineChecked
