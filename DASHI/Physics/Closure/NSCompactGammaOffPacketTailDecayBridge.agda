module DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit

------------------------------------------------------------------------
-- Order-theoretic form of a vanishing shell tail.
--
-- Analytically one wants
--
--   Tail(K,R) <= epsilon_R E_K ||h||_X,   epsilon_R -> 0.
--
-- Rather than smuggling a topology or a real limit into the abstract arithmetic,
-- this module records exactly the consequence used by absorption: every
-- admissible positive budget is reached at some radius.  The selected radius is
-- returned together with the full `OffPacketTailAbsorptionInputs` witness.
--
-- Proving that the concrete Fourier tail has this property remains the analytic
-- decay theorem.  This file only removes the later radius-selection seam.
------------------------------------------------------------------------

record RadiusIndexedOffPacketSplit
    {r : Level}
    (Radius : Set r)
    (A : AbsorptionArithmetic) : Set (lsuc r) where
  field
    splitAt : Radius → OffPacketSchurSplitInputs A

open RadiusIndexedOffPacketSplit public

record OrderVanishingTail
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A) : Set (lsuc r) where
  field
    AdmissibleTailBudget : Scalar A → Set

    tailEventuallyBelow :
      (budget : Scalar A) →
      AdmissibleTailBudget budget →
      Σ Radius
        (λ radius →
          _≤_ A
            (farShellTail (splitAt F radius))
            budget)

open OrderVanishingTail public

record TailAbsorptionTarget
    {r : Level}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F) : Set (lsuc r) where
  field
    absorbedTailBudget : Scalar A
    fullOffPacketBudget : Scalar A

    absorbedBudgetAdmissible :
      AdmissibleTailBudget V absorbedTailBudget

    schurPlusAbsorbedTailBelowFullBudget :
      (radius : Radius) →
      _≤_ A
        (_+_ A
          (schurWeightedBudget (splitAt F radius))
          absorbedTailBudget)
        fullOffPacketBudget

open TailAbsorptionTarget public

selectRadiusAndAssembleTailAbsorption :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F) →
  (T : TailAbsorptionTarget A F V) →
  Σ Radius
    (λ radius → OffPacketTailAbsorptionInputs A)
selectRadiusAndAssembleTailAbsorption A F V T
  with tailEventuallyBelow V
    (absorbedTailBudget T)
    (absorbedBudgetAdmissible T)
... | radius , tailBound =
  radius , record
    { tailSplitInputs = splitAt F radius
    ; absorbedTailBudget = absorbedTailBudget T
    ; fullOffPacketBudget = fullOffPacketBudget T
    ; farTailBelowAbsorbedBudget = tailBound
    ; schurPlusAbsorbedTailBelowFullBudget =
        schurPlusAbsorbedTailBelowFullBudget T radius
    }

selectedRadiusBoundsOffPacketResponse :
  ∀ {r}
    {Radius : Set r}
    (A : AbsorptionArithmetic)
    (F : RadiusIndexedOffPacketSplit Radius A)
    (V : OrderVanishingTail A F)
    (T : TailAbsorptionTarget A F V) →
  Σ Radius
    (λ radius →
      _≤_ A
        (offPacketResponse (splitAt F radius))
        (fullOffPacketBudget T))
selectedRadiusBoundsOffPacketResponse A F V T
  with selectRadiusAndAssembleTailAbsorption A F V T
... | radius , inputs =
  radius , absorbedTailBoundsOffPacketResponse A inputs
