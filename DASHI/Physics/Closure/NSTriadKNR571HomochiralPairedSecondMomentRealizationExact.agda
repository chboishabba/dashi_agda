module DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact where

------------------------------------------------------------------------
-- PUBLICATION-ORIENTED LOCAL SPLICE
--
-- Reuse, without duplicating, the existing theorem carriers:
--
--   R571 homochiral physical multiplier difference
--     -> Round27 signed radial translation commutator
--     -> old PairedCommutatorSample centered identity
--     -> old PairedSecondMomentSample quantitative carrier.
--
-- This owner deliberately does NOT claim the four Taylor/envelope inequalities,
-- a six-three gain, an inner-fibre summed estimate, R568, or any Clay endpoint.
-- It isolates the remaining same-object scalarization/magnitude bridge so those
-- inequalities can be proved on the literal physical carrier in the next slice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Pair
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

------------------------------------------------------------------------
-- 1. Literal Round27 scalar on the already-proved R571 homochiral radial route.
------------------------------------------------------------------------

r571Round27Scalar :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (shift : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (output : Z3.FourierMode) → ℚ
r571Round27Scalar sign S shift state output =
  R27.stateCoefficient
    (R27.translationMultiplierCommutator
      (Weld.radialMultiplier sign S) shift state)
    output

------------------------------------------------------------------------
-- 2. Same-object scalarization into the EXISTING paired-commutator carrier.
------------------------------------------------------------------------

record R571PairedTaylorRealization : Set₁ where
  field
    sign : R311.HelicitySign
    scalars : Helical.HelicalModeScalars Weld.F
    shift : Z3.FourierMode
    state : R27.FourierStateCarrier
    output : Z3.FourierMode
    pairedSample : Pair.PairedCommutatorSample

    -- This is the one same-object scalarization equation still requiring a
    -- literal physical y/-y realization.  It is intentionally visible.
    round27ScalarIsWeightedRawPair :
      r571Round27Scalar sign scalars shift state output
      ≡ Pair.weightedRawPair pairedSample

open R571PairedTaylorRealization public

r571PairedCenteredIdentity :
  (realization : R571PairedTaylorRealization) →
  r571Round27Scalar
      (sign realization)
      (scalars realization)
      (shift realization)
      (state realization)
      (output realization)
  ≡ Pair.weightedCenteredBranch (pairedSample realization)
    + Pair.weightedHighDifferenceBranch (pairedSample realization)
r571PairedCenteredIdentity realization =
  trans
    (round27ScalarIsWeightedRawPair realization)
    (Pair.weightedPairedCommutatorIdentity (pairedSample realization))

------------------------------------------------------------------------
-- 3. Quantitative scalar carrier: reuse the EXISTING second-moment sample.
------------------------------------------------------------------------

record R571PairedSecondMomentRealization : Set₁ where
  field
    taylor : R571PairedTaylorRealization
    secondMomentSample : Moment.PairedSecondMomentSample

    -- Least-privilege bridge: after the exact signed centered identity has
    -- happened, the scalar branches are dominated by the nonnegative magnitude
    -- carrier consumed by the old second-moment theorem.
    centeredBranchesBelowPairedMagnitude :
      Pair.weightedCenteredBranch (pairedSample taylor)
        + Pair.weightedHighDifferenceBranch (pairedSample taylor)
      ≤ Moment.pairedMagnitude secondMomentSample

open R571PairedSecondMomentRealization public

r571ScalarBelowPairedMagnitude :
  (realization : R571PairedSecondMomentRealization) →
  r571Round27Scalar
      (sign (taylor realization))
      (scalars (taylor realization))
      (shift (taylor realization))
      (state (taylor realization))
      (output (taylor realization))
  ≤ Moment.pairedMagnitude (secondMomentSample realization)
r571ScalarBelowPairedMagnitude realization
  rewrite r571PairedCenteredIdentity (taylor realization) =
  centeredBranchesBelowPairedMagnitude realization

r571PointwiseSecondMomentBound :
  (realization : R571PairedSecondMomentRealization) →
  (budget : Moment.PairedSecondMomentBudget) →
  r571Round27Scalar
      (sign (taylor realization))
      (scalars (taylor realization))
      (shift (taylor realization))
      (state (taylor realization))
      (output (taylor realization))
  ≤ Moment.weightedSecondMoment (secondMomentSample realization)
      * Moment.secondMomentCoefficient budget
r571PointwiseSecondMomentBound realization budget =
  ℚₚ.≤-trans
    (r571ScalarBelowPairedMagnitude realization)
    (Moment.pointwisePairedSecondMomentBound budget
      (secondMomentSample realization))

------------------------------------------------------------------------
-- Publication-facing status: carrier reuse is closed; physical quantitative
-- realization and R568 remain deliberately fail-closed.
------------------------------------------------------------------------

r571PairedCommutatorCarrierReused : Bool
r571PairedCommutatorCarrierReused = true

r571PairedSecondMomentCarrierReused : Bool
r571PairedSecondMomentCarrierReused = true

r571Round27SameObjectRouteRetained : Bool
r571Round27SameObjectRouteRetained = true

r571PhysicalPairedTaylorSampleClosed : Bool
r571PhysicalPairedTaylorSampleClosed = false

r571FourEnvelopeInequalitiesClosed : Bool
r571FourEnvelopeInequalitiesClosed = false

r571InnerFibreSummedGainClosed : Bool
r571InnerFibreSummedGainClosed = false

r571R568SpacetimeBudgetClosedHere : Bool
r571R568SpacetimeBudgetClosedHere = false
