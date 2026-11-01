module DASHI.Physics.Closure.NSTriadKNClayFrontierRound107Exact where

------------------------------------------------------------------------
-- ROUND107 / SERRIN-WIENER REDUCTION OF THE ROUND105 FORCING WALL
--
-- This round synchronizes the Agda frontier with the latest independent Lean
-- reconstruction of the literal Round105 Waleffe network-forcing problem.
--
-- The Lean lane proves on its finite Galerkin carrier the pointwise estimate
--
--   weightedPositiveNetworkForcing(t)
--     <= 3 W A(t)^2 L2(t) H1(t),
--
-- and hence the integrated reduction
--
--   weightedPositiveNetworkForcing[0,T]
--     <= 3 W integral A(t)^2 L2(t) H1(t) dt.
--
-- Here A is the Fourier/Wiener l1 amplitude, L2 is the energy norm and H1 is
-- the Dirichlet norm.  That Lean proof is not silently imported as an Agda
-- theorem.  Instead this module records the exact ordered reduction shape and
-- keeps the missing physical cutoff-uniform Serrin/Wiener expenditure visible.
--
-- IMPORTANT CROSS-CHECK
--
-- The Galerkin nonlinear energy cancellation rediscovered in Lean is already
-- theorem-bearing in Agda Round39 on the literal projected Galerkin carrier:
--
--   sum_k Re <u_k, P_NL_k> = 0.
--
-- We therefore reuse Round39 rather than introducing a duplicate energy
-- cancellation owner.
--
-- LIVE COUNTDOWN
--
-- The theorem-sized countdown remains TWO:
--
--   A. produce a cutoff-uniform physical bound for the Serrin/Wiener
--      expenditure integral sufficient for the positive Waleffe network
--      forcing budget;
--
--   B. instantiate the three-piece critical Sobolev/Simon upgrade on the exact
--      selected Galerkin family and exact G12 limiting solution.
--
-- No Clay promotion is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as Energy

three : ℚ
three = Int.+ 3 / 1

------------------------------------------------------------------------
-- Exact scalar shape of the sharpened forcing reduction.
--
-- `scaledWeight` is the factor `3 W` in the Lean realization.  We retain its
-- meaning explicitly instead of pretending the literal Lean carrier has been
-- imported into Agda.
------------------------------------------------------------------------

record SerrinWienerForcingReduction : Set where
  field
    networkForcing serrinWienerIntegral uniformExpenditure : ℚ
    weightCeiling scaledWeight : ℚ

    scaledWeightMeaning : scaledWeight ≡ three * weightCeiling
    scaledWeightNonnegative : 0ℚ ≤ scaledWeight

    forcingReducedToSerrinWiener :
      networkForcing ≤ scaledWeight * serrinWienerIntegral

    serrinWienerExpenditureBound :
      serrinWienerIntegral ≤ uniformExpenditure

open SerrinWienerForcingReduction public

networkForcingPaidByUniformSerrinWienerExpenditure :
  (R : SerrinWienerForcingReduction) →
  networkForcing R ≤ scaledWeight R * uniformExpenditure R
networkForcingPaidByUniformSerrinWienerExpenditure R =
  let
    instance scaledWeightNNI : NonNegative (scaledWeight R)
    scaledWeightNNI = nonNegative (scaledWeightNonnegative R)
  in
  ℚP.≤-trans
    (forcingReducedToSerrinWiener R)
    (ℚP.*-monoˡ-≤-nonNeg
      (scaledWeight R)
      (serrinWienerExpenditureBound R))

------------------------------------------------------------------------
-- Cross-language frontier status.
------------------------------------------------------------------------

round107ProjectedGalerkinEnergyCancellationClosed : Bool
round107ProjectedGalerkinEnergyCancellationClosed =
  Energy.f4GlobalOutputFiberPartitionClosed

round107SerrinWienerForcingReductionShapeClosed : Bool
round107SerrinWienerForcingReductionShapeClosed = true

-- This is the actual new physical producer exposed by the Lean reduction.
-- It remains open for arbitrary smooth periodic data uniformly in cutoff.
round107PhysicalUniformSerrinWienerExpenditureClosed : Bool
round107PhysicalUniformSerrinWienerExpenditureClosed = false

round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed : Bool
round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed =
  R106.round106PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed

round107UniformGalerkinCriticalBarrierClosed : Bool
round107UniformGalerkinCriticalBarrierClosed =
  R106.round106UniformGalerkinCriticalBarrierClosed

round107PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round107PhysicalCriticalSobolevSimonUpgradeClosed =
  R106.round106PhysicalCriticalSobolevSimonUpgradeClosed

round107CurrentTheoremSizedObligationCount : Nat
round107CurrentTheoremSizedObligationCount = 2

------------------------------------------------------------------------
-- Regression equalities.
------------------------------------------------------------------------

round107ProjectedGalerkinEnergyCancellationClosedIsTrue :
  round107ProjectedGalerkinEnergyCancellationClosed ≡ true
round107ProjectedGalerkinEnergyCancellationClosedIsTrue = refl

round107SerrinWienerForcingReductionShapeClosedIsTrue :
  round107SerrinWienerForcingReductionShapeClosed ≡ true
round107SerrinWienerForcingReductionShapeClosedIsTrue = refl

round107PhysicalUniformSerrinWienerExpenditureClosedIsFalse :
  round107PhysicalUniformSerrinWienerExpenditureClosed ≡ false
round107PhysicalUniformSerrinWienerExpenditureClosedIsFalse = refl

round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosedIsFalse :
  round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosed ≡ false
round107PhysicalWeightedPositiveWaleffeNetworkForcingBudgetClosedIsFalse = refl

round107UniformGalerkinCriticalBarrierClosedIsFalse :
  round107UniformGalerkinCriticalBarrierClosed ≡ false
round107UniformGalerkinCriticalBarrierClosedIsFalse = refl

round107PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round107PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round107PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl

round107CurrentTheoremSizedObligationCountIsTwo :
  round107CurrentTheoremSizedObligationCount ≡ 2
round107CurrentTheoremSizedObligationCountIsTwo = refl

round107ClayPromotion : Bool
round107ClayPromotion = false

round107ClayPromotionIsFalse : round107ClayPromotion ≡ false
round107ClayPromotionIsFalse = refl
