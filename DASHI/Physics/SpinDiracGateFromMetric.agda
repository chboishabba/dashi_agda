module DASHI.Physics.SpinDiracGateFromMetric where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.QuadraticForm using (ScalarField)
open import DASHI.Geometry.OrthogonalityFromPolarization using (Polarization)
open import DASHI.Geometry.CliffordGate using (BilinearForm; RingLike; CliffordAlgebra)
open import DASHI.Geometry.SpinGate using (SpinGroup; DiracFromMetric)

------------------------------------------------------------------------
-- Tie the Clifford/Spin/Dirac gates directly to the forced metric
-- coming from polarization (⟪_,_⟫). This is interface-only and
-- introduces no postulates.

record ForcedBilinear
  {ℓv ℓs : Level}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (Pol : Polarization A F)
  : Set (lsuc (ℓv ⊔ ℓs)) where
  B : BilinearForm (Additive.Carrier A) (ScalarField.S F)
  B = record { ⟪_,_⟫ = Polarization.⟪_,_⟫ Pol }

open ForcedBilinear public

record SpinDiracGateFromMetric
  {ℓv ℓs ℓa ℓg ℓψ : Level}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (Pol : Polarization A F)
  (R : RingLike (ScalarField.S F))
  (Ψ : Set ℓψ)
  : Set (lsuc (ℓv ⊔ ℓs ⊔ ℓa ⊔ ℓg ⊔ ℓψ)) where

  field
    forcedBilinear : ForcedBilinear A F Pol
  field
    clifford : CliffordAlgebra {ℓa = ℓa} (Additive.Carrier A) (ScalarField.S F) R (ForcedBilinear.B forcedBilinear)
    spin     : SpinGroup {ℓa = ℓa} {ℓg = ℓg}
               (Additive.Carrier A) (ScalarField.S F) R (ForcedBilinear.B forcedBilinear) clifford
    dirac    : DiracFromMetric {ℓa = ℓa} {ℓψ = ℓψ}
               (Additive.Carrier A) (ScalarField.S F) Ψ R (ForcedBilinear.B forcedBilinear) clifford

open SpinDiracGateFromMetric public
