module DASHI.Physics.Closure.NSPeriodicWeightedEnvelopeLimitTransport where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Continuum transport through the weighted shell envelope.
--
-- Direct L1_t L-infinity_x lower semicontinuity is not assumed.  Instead the
-- continuum envelope is the least upper bound of its finite shell partial
-- sums.  Fixed-shell convergence and finite-partial lower semicontinuity give
-- a common cutoff-independent upper bound for every partial sum; the least
-- upper bound property then gives the full envelope bound, followed by the
-- vorticity reconstruction estimate.
------------------------------------------------------------------------

record PeriodicWeightedEnvelopeLimitInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    continuumPartialEnvelope : Nat → Scalar A
    continuumFullEnvelope : Scalar A
    cutoffUniformEnvelopeBound : Scalar A
    continuumVorticityExpenditure : Scalar A

    FixedShellConvergence : Set
    FinitePartialLowerSemicontinuity : Set

    fixedShellConvergence : FixedShellConvergence
    finitePartialLowerSemicontinuity : FinitePartialLowerSemicontinuity

    finitePartialPassesToUniformBound :
      FixedShellConvergence →
      FinitePartialLowerSemicontinuity →
      ∀ n →
      _≤_ A
        (continuumPartialEnvelope n)
        cutoffUniformEnvelopeBound

    fullEnvelopeLeastUpperBound :
      ∀ upper →
      (∀ n → _≤_ A (continuumPartialEnvelope n) upper) →
      _≤_ A continuumFullEnvelope upper

    continuumVorticityReconstruction :
      _≤_ A continuumVorticityExpenditure continuumFullEnvelope

    ContinuumVorticityExpenditureFinite : Set

    uniformBoundImpliesFinite :
      _≤_ A
        continuumVorticityExpenditure
        cutoffUniformEnvelopeBound →
      ContinuumVorticityExpenditureFinite

open PeriodicWeightedEnvelopeLimitInputs public

allContinuumPartialEnvelopesBelowUniformBound :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicWeightedEnvelopeLimitInputs A) →
  ∀ n →
  _≤_ A
    (continuumPartialEnvelope L n)
    (cutoffUniformEnvelopeBound L)
allContinuumPartialEnvelopesBelowUniformBound L =
  finitePartialPassesToUniformBound L
    (fixedShellConvergence L)
    (finitePartialLowerSemicontinuity L)

continuumFullEnvelopeBelowUniformCutoffBound :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicWeightedEnvelopeLimitInputs A) →
  _≤_ A
    (continuumFullEnvelope L)
    (cutoffUniformEnvelopeBound L)
continuumFullEnvelopeBelowUniformCutoffBound L =
  fullEnvelopeLeastUpperBound L
    (cutoffUniformEnvelopeBound L)
    (allContinuumPartialEnvelopesBelowUniformBound L)

continuumVorticityBelowUniformCutoffBound :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicWeightedEnvelopeLimitInputs A) →
  _≤_ A
    (continuumVorticityExpenditure L)
    (cutoffUniformEnvelopeBound L)
continuumVorticityBelowUniformCutoffBound {A = A} L =
  ≤-trans A
    (continuumVorticityReconstruction L)
    (continuumFullEnvelopeBelowUniformCutoffBound L)

weightedEnvelopeTransportGivesFiniteContinuumVorticity :
  ∀ {A : AbsorptionArithmetic} →
  (L : PeriodicWeightedEnvelopeLimitInputs A) →
  ContinuumVorticityExpenditureFinite L
weightedEnvelopeTransportGivesFiniteContinuumVorticity L =
  uniformBoundImpliesFinite L
    (continuumVorticityBelowUniformCutoffBound L)

------------------------------------------------------------------------
-- Status: countable-envelope reconstruction from finite partial limits is
-- checked.  The analytic leaves are fixed-shell convergence and finite-partial
-- lower semicontinuity for the literal dyadic partition in the selected
-- Galerkin family.
------------------------------------------------------------------------

weightedEnvelopeLimitTransportAssemblyLevel : ProofLevel
weightedEnvelopeLimitTransportAssemblyLevel = machineChecked
