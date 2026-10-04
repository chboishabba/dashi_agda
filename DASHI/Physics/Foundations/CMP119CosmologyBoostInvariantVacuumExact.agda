{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact where

------------------------------------------------------------------------
-- ONE NONTRIVIAL LORENTZ BOOST + ISOTROPY -> VACUUM EQUATION OF STATE.
--
-- For an isotropic contravariant stress in a local Lorentz frame,
--
--   T = diag(rho,p,p,p),
--
-- the 0-1 component after a boost with
--
--   gamma = 5/3,   gamma*v = 4/3
--
-- is (up to the conventional overall sign)
--
--   T'01 = -(20/9) (rho + p).
--
-- The exact boost satisfies gamma^2 - (gamma*v)^2 = 1.
-- If the selected vacuum stress is invariant under this NONTRIVIAL boost,
-- its off-diagonal component remains zero, hence rho + p = 0 and p = -rho.
--
-- This is the concrete algebraic content needed by the cosmology vacuum
-- branch.  It does NOT prove that the reconstructed CMP119 state is invariant
-- under this boost; that same-state physical theorem remains the source seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

boostGamma : ℚ
boostGamma = + 5 / 3

boostGammaV : ℚ
boostGammaV = + 4 / 3

boostCrossCoefficient : ℚ
boostCrossCoefficient = + 20 / 9

boostCrossInverse : ℚ
boostCrossInverse = + 9 / 20

selectedBoostIsLorentz :
  boostGamma * boostGamma - boostGammaV * boostGammaV ≡ 1ℚ
selectedBoostIsLorentz =
  Ring.solve []

selectedBoostCoefficientInvertible :
  boostCrossInverse * boostCrossCoefficient ≡ 1ℚ
selectedBoostCoefficientInvertible =
  Ring.solve []

boosted01 :
  Vacuum.IsotropicLorentzianStress → ℚ
boosted01 stress =
  - (boostCrossCoefficient
      * (Vacuum.rho stress + Vacuum.pressure stress))

record SelectedBoostInvariantIsotropicStress : Set where
  field
    stress : Vacuum.IsotropicLorentzianStress

    -- The unboosted isotropic tensor has T01 = 0, and invariance under the
    -- selected nontrivial boost requires the transformed T'01 to remain zero.
    selectedBoostOffDiagonalInvariant :
      boosted01 stress ≡ 0ℚ

open SelectedBoostInvariantIsotropicStress public

boostInvarianceForcesRhoPlusPressureZero :
  ∀ invariant →
  Vacuum.rho (stress invariant)
    + Vacuum.pressure (stress invariant)
  ≡ 0ℚ
boostInvarianceForcesRhoPlusPressureZero invariant =
  let
    x = Vacuum.rho (stress invariant)
      + Vacuum.pressure (stress invariant)

    negScaledZero :
      - (boostCrossCoefficient * x) ≡ 0ℚ
    negScaledZero =
      selectedBoostOffDiagonalInvariant invariant

    scaledZero :
      boostCrossCoefficient * x ≡ 0ℚ
    scaledZero =
      trans
        (Ring.solve-∀ boostCrossCoefficient x)
        (trans
          (cong -_ negScaledZero)
          (Ring.solve []))

    inverseScaled :
      boostCrossInverse * (boostCrossCoefficient * x)
      ≡ boostCrossInverse * 0ℚ
    inverseScaled =
      cong (boostCrossInverse *_) scaledZero
  in
  trans
    (sym (Ring.solve-∀ x))
    (trans
      inverseScaled
      (Ring.solve []))

boostInvarianceForcesVacuumEquationOfState :
  ∀ invariant →
  Vacuum.pressure (stress invariant)
  ≡ - Vacuum.rho (stress invariant)
boostInvarianceForcesVacuumEquationOfState invariant =
  let
    rho = Vacuum.rho (stress invariant)
    p = Vacuum.pressure (stress invariant)

    zeroSum : rho + p ≡ 0ℚ
    zeroSum =
      boostInvarianceForcesRhoPlusPressureZero invariant
  in
  trans
    (Ring.solve-∀ rho p)
    (trans
      (cong (λ sum → sum - rho) zeroSum)
      (Ring.solve-∀ rho))

asVacuumLikeLorentzianStress :
  SelectedBoostInvariantIsotropicStress →
  Vacuum.VacuumLikeLorentzianStress
asVacuumLikeLorentzianStress invariant = record
  { Vacuum.VacuumLikeLorentzianStress.stress =
      stress invariant
  ; Vacuum.VacuumLikeLorentzianStress.pressureIsMinusRho =
      boostInvarianceForcesVacuumEquationOfState invariant
  }

boostInvariantTraceIsTwiceActive :
  ∀ invariant →
  Vacuum.trace (stress invariant)
  ≡
  Vacuum.activeStress (stress invariant)
  + Vacuum.activeStress (stress invariant)
boostInvariantTraceIsTwiceActive invariant =
  Vacuum.vacuumTraceIsTwiceActive
    (asVacuumLikeLorentzianStress invariant)

------------------------------------------------------------------------
-- FRONTIER FLAGS
------------------------------------------------------------------------

oneNontrivialBoostPlusIsotropyForcesVacuumEquationOfState : Bool
oneNontrivialBoostPlusIsotropyForcesVacuumEquationOfState = true

selectedCMP119BoostInvarianceStillRequiresReconstructedStateTheorem : Bool
selectedCMP119BoostInvarianceStillRequiresReconstructedStateTheorem = true

isotropyAloneSuffices : Bool
isotropyAloneSuffices = false
