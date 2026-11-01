module DASHI.Crypto.MLKEMFinitePriorSuccessMassExact where

------------------------------------------------------------------------
-- FINITE PRIOR SUCCESS-MASS CAPACITY
--
-- The state/transcript result bounds how many protected labels an exact finite
-- architecture can distinguish.  For average-case recovery we need one more
-- finite combinatorial step: a set of at most C labels captures at most
--
--     C * w_max
--
-- prior weight when every individual protected label has weight at most w_max.
--
-- We keep the statement division-free.  `successWeight` and `maxPointWeight`
-- are integer numerators with respect to one common total prior weight.  Thus
-- the theorem does not depend on a rational-number implementation and can be
-- instantiated directly by CBD raw-bit multiplicities.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _*_)
import Data.Nat.Properties as NatP

successMassBound :
  (successCount capacity maxPointWeight successWeight : Nat) →
  successCount ≤ capacity →
  successWeight ≤ successCount * maxPointWeight →
  successWeight ≤ capacity * maxPointWeight
successMassBound
  successCount capacity maxPointWeight successWeight
  successWithinCapacity massWithinCount =
  NatP.≤-trans
    massWithinCount
    (NatP.*-monoˡ-≤ maxPointWeight successWithinCapacity)

record FinitePriorSuccessMass : Set where
  constructor finite-prior-success-mass
  field
    successCount : Nat
    capacity : Nat
    maxPointWeight : Nat
    successWeight : Nat

    successCountWithinCapacity : successCount ≤ capacity
    successfulSetWeightBound :
      successWeight ≤ successCount * maxPointWeight

open FinitePriorSuccessMass public

successWeightWithinCapacityMass :
  (certificate : FinitePriorSuccessMass) →
  successWeight certificate ≤
    capacity certificate * maxPointWeight certificate
successWeightWithinCapacityMass certificate =
  successMassBound
    (successCount certificate)
    (capacity certificate)
    (maxPointWeight certificate)
    (successWeight certificate)
    (successCountWithinCapacity certificate)
    (successfulSetWeightBound certificate)

------------------------------------------------------------------------
-- Capacity adapter.
--
-- Frequently the architecture gives an intermediate code-capacity bound C0
-- and the successful protected set is only known to inject into a code carrier
-- of size <= C0.  Keeping the two inequalities separate makes the exact
-- semantic producer visible.
------------------------------------------------------------------------

successMassViaCodeCarrier :
  (successCount codeCount capacity maxPointWeight successWeight : Nat) →
  successCount ≤ codeCount →
  codeCount ≤ capacity →
  successWeight ≤ successCount * maxPointWeight →
  successWeight ≤ capacity * maxPointWeight
successMassViaCodeCarrier
  successCount codeCount capacity maxPointWeight successWeight
  successIntoCode codeIntoCapacity massWithinCount =
  successMassBound
    successCount capacity maxPointWeight successWeight
    (NatP.≤-trans successIntoCode codeIntoCapacity)
    massWithinCount

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This theorem does not assert that ML-KEM's secret prior is uniform, nor that
-- every architecture succeeds on exactly `capacity` labels.  A source-specific
-- producer must supply:
--
--   * the actual successful protected-label count (or an upper bound);
--   * a common integer weighting of the prior;
--   * a maximum individual-label weight in that weighting.
--
-- The result then bounds average success mass rather than merely support-wide
-- exact recovery.
------------------------------------------------------------------------
