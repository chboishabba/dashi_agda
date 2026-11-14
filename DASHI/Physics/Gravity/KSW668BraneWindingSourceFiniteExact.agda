module DASHI.Physics.Gravity.KSW668BraneWindingSourceFiniteExact where

------------------------------------------------------------------------
-- Original KSW/KK BRANE PROBE-WORLDVOLUME positive-energy source receipt.
--
-- Positive tension T, winding scalar chi=n theta, rigidity f:
--   E(R) = pi*(2*T*R + f²*n²/R).
-- Uniform radial equation, equivalent to the cylinder normal shape
-- equation S^{ab} K_ab=0:
--   2*T*R² = f²*n².
--
-- For T=2, f=2, n=1, R=1, both sides are 4.
-- E(R)/pi = 2*T*R + f²*n²/R = 8 at equilibrium.
-- This is the exact integer part; analytic variation, second
-- derivative, null-energy positivity and 5D massless wave PDE
-- are tested by scripts/ksw668_brane_winding_stability_source.py.
--
-- No pi-as-rational fiction, no gravitational backreaction/Israel
-- junction, all-mode stability, bulk field coupling, or observed
-- transport claim is made by this finite model.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

tension : Nat
tension = 2

rigidity : Nat
rigidity = 2

winding : Nat
winding = 1

equilibriumRadius : Nat
equilibriumRadius = 1

twoTensionTimesRSquared : Nat
twoTensionTimesRSquared =
  2 * tension * (equilibriumRadius * equilibriumRadius)

windingRigiditySquared : Nat
windingRigiditySquared =
  (rigidity * rigidity) * (winding * winding)

genuineNonzeroSourceRadialBalance :
  twoTensionTimesRSquared ≡ windingRigiditySquared
genuineNonzeroSourceRadialBalance = refl

sourceBalanceNumeratorIsFour :
  twoTensionTimesRSquared ≡ 4
sourceBalanceNumeratorIsFour = refl

windingBalanceNumeratorIsFour :
  windingRigiditySquared ≡ 4
windingBalanceNumeratorIsFour = refl

-- R=1 removes the denominator in the energy-per-area/pi formula.
sourceEnergyPerAreaDividedByPi : Nat
sourceEnergyPerAreaDividedByPi =
  2 * tension * equilibriumRadius + windingRigiditySquared

sourcePositiveEnergyEight :
  sourceEnergyPerAreaDividedByPi ≡ 8
sourcePositiveEnergyEight = refl

sourceShapeForceCancelsAtEquilibrium :
  twoTensionTimesRSquared
    ≡ windingRigiditySquared
sourceShapeForceCancelsAtEquilibrium =
  genuineNonzeroSourceRadialBalance

sourceHasNoNegativeTensionFixture :
  tension ≡ 0 → ⊥
sourceHasNoNegativeTensionFixture ()

-- Only a real-valued, differentiable brane-worldvolume action and
-- same-metric Einstein matter allow a physical dynamical upgrade.
