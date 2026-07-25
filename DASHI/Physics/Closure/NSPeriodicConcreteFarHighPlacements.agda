module DASHI.Physics.Closure.NSPeriodicConcreteFarHighPlacements where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Fold
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal two-placement owner for the far-high interaction.
------------------------------------------------------------------------

record FarHighPlacementFamily
    {i : Level}
    (A : AbsorptionArithmetic)
    (Item : Set i) : Set i where
  field
    items : List Item
    leftContribution rightContribution : Item → Scalar A

open FarHighPlacementFamily public

leftPlacement rightPlacement :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  FarHighPlacementFamily A Item → Scalar A
leftPlacement F = Fold.sumBy (leftContribution F) (items F)
rightPlacement F = Fold.sumBy (rightContribution F) (items F)

farHighTotal :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  FarHighPlacementFamily A Item → Scalar A
farHighTotal {A = A} F = _+_ A (leftPlacement F) (rightPlacement F)

exactTwoPlacementDecomposition :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (F : FarHighPlacementFamily A Item) →
  farHighTotal F ≡ _+_ A (leftPlacement F) (rightPlacement F)
exactTwoPlacementDecomposition F = refl

concreteFarHighPlacementsLevel : ProofLevel
concreteFarHighPlacementsLevel = machineChecked
