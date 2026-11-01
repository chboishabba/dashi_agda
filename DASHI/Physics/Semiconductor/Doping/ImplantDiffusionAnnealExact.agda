{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Doping.ImplantDiffusionAnnealExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Finite process carrier for ion implantation followed by redistribution and
-- activation.  The owner separates implanted inventory, retained inventory,
-- activated inventory and redistributed inventory; detailed stopping/range and
-- diffusion laws remain residual.

record ImplantState : Set where
  constructor implantState
  field
    incidentIons    : Nat
    retainedIons    : Nat
    lostOrReflected : Nat
    accounting      : retainedIons + lostOrReflected ≡ incidentIons

open ImplantState public

syntheticImplant : ImplantState
syntheticImplant = implantState 100 82 18 refl

record AnnealState : Set where
  constructor annealState
  field
    retainedBefore : Nat
    activeAfter     : Nat
    inactiveAfter   : Nat
    activationAccounting : activeAfter + inactiveAfter ≡ retainedBefore

open AnnealState public

syntheticAnneal : AnnealState
syntheticAnneal = annealState 82 70 12 refl

-- Equal implanted/retained inventory does not determine equal electrical
-- activation after anneal.
annealA : AnnealState
annealA = annealState 82 70 12 refl

annealB : AnnealState
annealB = annealState 82 50 32 refl

sameRetainedInventory : retainedBefore annealA ≡ retainedBefore annealB
sameRetainedInventory = refl

data ⊥ : Set where

retainedInventoryDoesNotDetermineActivation : activeAfter annealA ≡ activeAfter annealB → ⊥
retainedInventoryDoesNotDetermineActivation ()

-- A coarse diffusion-width relation for later replacement by a proper PDE/
-- Green-function producer.  widthCode is represented against diffusivity/time
-- codes only as an exact bookkeeping seam.
record DiffusionBudget : Set where
  constructor diffusionBudget
  field
    diffusivityCode : Nat
    timeCode        : Nat
    budgetCode      : Nat
    relation        : diffusivityCode * timeCode ≡ budgetCode

open DiffusionBudget public

syntheticDiffusionBudget : DiffusionBudget
syntheticDiffusionBudget = diffusionBudget 4 25 100 refl

data DopingResidual : Set where
  ImplantEnergyDistribution : DopingResidual
  ImplantAngle : DopingResidual
  Channeling : DopingResidual
  StoppingPower : DopingResidual
  ProjectedRange : DopingResidual
  RangeStraggle : DopingResidual
  DamageProfile : DopingResidual
  TransientEnhancedDiffusion : DopingResidual
  DopantDiffusivity : DopingResidual
  Clustering : DopingResidual
  ElectricalActivationLaw : DopingResidual
  ExactAnnealThermalHistory : DopingResidual
