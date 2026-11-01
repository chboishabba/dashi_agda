module DASHI.Crypto.ObservationAcquisitionCostExact where

------------------------------------------------------------------------
-- OBSERVATION ACQUISITION COST VS RECOVERY COST
--
-- Blue-team refinement of AlgorithmRelativeRecoveryCostExact.  A candidate
-- fibre may shrink and the post-observation search may be cheaper, yet the
-- observation itself has acquisition/query cost.  The correct comparison is
-- therefore
--
--   recovery-before
--   versus
--   observation-cost + recovery-after.
--
-- This is exact Nat accounting, not an attack-complexity claim until a concrete
-- observation/query procedure supplies the costs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Crypto.AlgorithmRelativeRecoveryCostExact as Recovery
import DASHI.Crypto.FiniteMLWEPriorScoreSearchRegressionExact as Lab

record ObservationAcquisitionComparison : Set where
  constructor observationAcquisitionComparison
  field
    before after : Recovery.RecoveryArchitecture
    observationCost : Nat

open ObservationAcquisitionComparison public

afterWithObservationCost : ObservationAcquisitionComparison → Nat
afterWithObservationCost comparison =
  observationCost comparison + Recovery.totalRecoveryCost (after comparison)

record NetBeneficialObservation
    (comparison : ObservationAcquisitionComparison) : Set where
  constructor netBeneficialObservation
  field
    netGain : Nat
    exactBenefitAccounting :
      Recovery.totalRecoveryCost (before comparison)
      ≡ afterWithObservationCost comparison + netGain

open NetBeneficialObservation public

record NetHarmfulObservation
    (comparison : ObservationAcquisitionComparison) : Set where
  constructor netHarmfulObservation
  field
    extraCost : Nat
    exactHarmAccounting :
      afterWithObservationCost comparison
      ≡ Recovery.totalRecoveryCost (before comparison) + extraCost

open NetHarmfulObservation public

------------------------------------------------------------------------
-- Concrete composition with the existing finite 2x2 MLWE laboratory.
--
-- The hidden-dependent observation reduces recovery cost 13 -> 8.  If the
-- observation itself costs 2 units, the complete route costs 10 and earns a
-- net gain of 3.  If acquisition costs 6, complete work becomes 14 and the
-- same candidate shrink is net harmful by 1.
------------------------------------------------------------------------

cheapLabObservation : ObservationAcquisitionComparison
cheapLabObservation =
  observationAcquisitionComparison
    Lab.labBeforeObservation
    Lab.labAfterObservation
    2

cheapLabObservationTotal : afterWithObservationCost cheapLabObservation ≡ 10
cheapLabObservationTotal = refl

cheapLabObservationNetGain : NetBeneficialObservation cheapLabObservation
cheapLabObservationNetGain = netBeneficialObservation 3 refl

expensiveLabObservation : ObservationAcquisitionComparison
expensiveLabObservation =
  observationAcquisitionComparison
    Lab.labBeforeObservation
    Lab.labAfterObservation
    6

expensiveLabObservationTotal :
  afterWithObservationCost expensiveLabObservation ≡ 14
expensiveLabObservationTotal = refl

expensiveLabObservationIsNetHarmful :
  NetHarmfulObservation expensiveLabObservation
expensiveLabObservationIsNetHarmful = netHarmfulObservation 1 refl

------------------------------------------------------------------------
-- Net value-of-information carrier.
------------------------------------------------------------------------

netAlgorithmRelativeGain :
  ∀ {comparison} → NetBeneficialObservation comparison → Nat
netAlgorithmRelativeGain benefit = netGain benefit
