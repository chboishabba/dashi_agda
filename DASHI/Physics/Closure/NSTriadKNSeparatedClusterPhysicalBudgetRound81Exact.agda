module DASHI.Physics.Closure.NSTriadKNSeparatedClusterPhysicalBudgetRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / SEPARATED-CLUSTER C4 WELD
--
-- This module composes the exact cluster Sylvester estimate with the exact
-- three-term off-block strain forcing decomposition.  It is the theorem-level
-- replacement for the old receipt statement "pressure correction divided by
-- eigenvalue gap".
--
-- Inputs are same-coordinate equalities identifying the two Sylvester forcing
-- entries with the two physical material-strain off-block entries.  Then
--
--   delta^2 * projectorRateEnergy
--       <= forcingEnergy
--       <= 3(localVorticity + pressureHessian + viscous).
--
-- The only remaining C4a PDE task is therefore to instantiate these entries on
-- the selected Galerkin trajectory and prove a cutoff-uniform budget for the
-- pressure-Hessian and viscous square energies (the local vorticity piece has
-- its own exact alignment-defect identity in Round81).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNClusterSylvesterBudgetRound81Exact as Syl
import DASHI.Physics.Closure.NSTriadKNClusterForcingThreeTermBudgetRound81Exact as Force

record SeparatedClusterPhysicalBudget : Set where
  field
    separatedSylvester : Syl.SeparatedTwoCoordinateClusterSylvester
    physicalForcing : Force.TwoCoordinateThreeTermForcing

    forcingAMatchesPhysical :
      Syl.forcingA (Syl.sylvester separatedSylvester)
      ≡ Force.totalA physicalForcing

    forcingBMatchesPhysical :
      Syl.forcingB (Syl.sylvester separatedSylvester)
      ≡ Force.totalB physicalForcing

open SeparatedClusterPhysicalBudget public

sylvesterForcingEnergyMatchesPhysical :
  (datum : SeparatedClusterPhysicalBudget) →
  Syl.forcingSquareEnergy (Syl.sylvester (separatedSylvester datum))
  ≡ Force.totalSquareEnergy (physicalForcing datum)
sylvesterForcingEnergyMatchesPhysical datum =
  subst
    (λ a →
      Syl.square a
        + Syl.square (Syl.forcingB (Syl.sylvester (separatedSylvester datum)))
      ≡ Force.totalSquareEnergy (physicalForcing datum))
    (forcingAMatchesPhysical datum)
    (subst
      (λ b →
        Syl.square (Force.totalA (physicalForcing datum)) + Syl.square b
        ≡ Force.totalSquareEnergy (physicalForcing datum))
      (forcingBMatchesPhysical datum)
      refl)

separatedClusterProjectorRatePhysicalBudget :
  (datum : SeparatedClusterPhysicalBudget) →
  Syl.square (Syl.threshold (separatedSylvester datum))
    * Syl.projectorRateSquareEnergy
      (Syl.sylvester (separatedSylvester datum))
  ≤ Force.three *
    (Force.localSquareEnergy (physicalForcing datum)
      + Force.pressureSquareEnergy (physicalForcing datum)
      + Force.viscousSquareEnergy (physicalForcing datum))
separatedClusterProjectorRatePhysicalBudget datum =
  let
    spectral :
      Syl.square (Syl.threshold (separatedSylvester datum))
        * Syl.projectorRateSquareEnergy
          (Syl.sylvester (separatedSylvester datum))
      ≤ Syl.forcingSquareEnergy
          (Syl.sylvester (separatedSylvester datum))
    spectral = Syl.thresholdSquaredProjectorRateEnergyBound
      (separatedSylvester datum)

    physical :
      Force.totalSquareEnergy (physicalForcing datum)
      ≤ Force.three *
        (Force.localSquareEnergy (physicalForcing datum)
          + Force.pressureSquareEnergy (physicalForcing datum)
          + Force.viscousSquareEnergy (physicalForcing datum))
    physical = Force.twoCoordinateThreeTermForcingBound (physicalForcing datum)

    forcingPhysical :
      Syl.forcingSquareEnergy
        (Syl.sylvester (separatedSylvester datum))
      ≤ Force.three *
        (Force.localSquareEnergy (physicalForcing datum)
          + Force.pressureSquareEnergy (physicalForcing datum)
          + Force.viscousSquareEnergy (physicalForcing datum))
    forcingPhysical =
      subst
        (λ lower →
          lower ≤ Force.three *
            (Force.localSquareEnergy (physicalForcing datum)
              + Force.pressureSquareEnergy (physicalForcing datum)
              + Force.viscousSquareEnergy (physicalForcing datum)))
        (sym (sylvesterForcingEnergyMatchesPhysical datum))
        physical
  in
  ℚP.≤-trans spectral forcingPhysical

round81SeparatedClusterAbstractC4ClosedToPhysicalBudget : Bool
round81SeparatedClusterAbstractC4ClosedToPhysicalBudget = true

round81SeparatedClusterAbstractC4ClosedToPhysicalBudgetIsTrue :
  round81SeparatedClusterAbstractC4ClosedToPhysicalBudget ≡ true
round81SeparatedClusterAbstractC4ClosedToPhysicalBudgetIsTrue = refl
