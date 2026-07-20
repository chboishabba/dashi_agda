module DASHI.Physics.Closure.NSDivergenceFreePolarizationBasis where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel

------------------------------------------------------------------------
-- A proof-relevant polarization basis transverse to each nonzero mode.
------------------------------------------------------------------------

record DivergenceFreePolarizationBasis
    {m v s l : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s)
    (Label : Set l)
    (laws : FourierVectorLaws Mode Vector Scalar) :
    Set (lsuc (m ⊔ v ⊔ s ⊔ l)) where
  field
    basisVector : Mode → Label → Vector

    basisDivergenceFree :
      ∀ mode label →
      vectorDot laws
        (waveVector laws mode)
        (basisVector mode label)
      ≡ scalarZero laws

open DivergenceFreePolarizationBasis public

record SelectedPolarizations
    {m v s l : Level}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    {Label : Set l}
    {laws : FourierVectorLaws Mode Vector Scalar}
    (basis : DivergenceFreePolarizationBasis Mode Vector Scalar Label laws) :
    Set (lsuc (m ⊔ v ⊔ s ⊔ l)) where
  field
    backgroundLabel : Mode → Label
    perturbationLabel : Mode → Label

open SelectedPolarizations public

selectedBackgroundPolarization :
  ∀ {m v s l}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    {Label : Set l}
    {laws : FourierVectorLaws Mode Vector Scalar}
    (basis : DivergenceFreePolarizationBasis Mode Vector Scalar Label laws) →
  SelectedPolarizations basis →
  Mode → Vector
selectedBackgroundPolarization basis selection mode =
  basisVector basis mode (backgroundLabel selection mode)

selectedPerturbationPolarization :
  ∀ {m v s l}
    {Mode : Set m}
    {Vector : Set v}
    {Scalar : Set s}
    {Label : Set l}
    {laws : FourierVectorLaws Mode Vector Scalar}
    (basis : DivergenceFreePolarizationBasis Mode Vector Scalar Label laws) →
  SelectedPolarizations basis →
  Mode → Vector
selectedPerturbationPolarization basis selection mode =
  basisVector basis mode (perturbationLabel selection mode)
