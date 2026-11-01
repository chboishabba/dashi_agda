module DASHI.Physics.Closure.NSWall1PolarizationInstantiation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice using (FourierMode)
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel
open import DASHI.Physics.Closure.NSDivergenceFreePolarizationBasis
open import DASHI.Physics.Closure.NSWall1FourierShellInstance

------------------------------------------------------------------------
-- Identify the Wall-1 background and perturbation polarizations with a
-- divergence-free basis selected mode by mode.
------------------------------------------------------------------------

record Wall1PolarizationBasisMatch
    {v s l : Level}
    {Vector : Set v}
    {Scalar : Set s}
    (Label : Set l)
    (W : Wall1FourierShellData Vector Scalar) :
    Set (lsuc (v ⊔ s ⊔ l)) where
  field
    basis :
      DivergenceFreePolarizationBasis
        FourierMode Vector Scalar Label (laws W)

    selection : SelectedPolarizations basis

    backgroundPolarizationMatches :
      ∀ mode →
      backgroundPolarization W mode ≡
      selectedBackgroundPolarization basis selection mode

    perturbationPolarizationMatches :
      ∀ mode →
      perturbationPolarization W mode ≡
      selectedPerturbationPolarization basis selection mode

open Wall1PolarizationBasisMatch public
