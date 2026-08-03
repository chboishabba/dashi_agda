module DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Record the literal nonlinear identity used in Proposition 3.1.  This is not
-- a generic Bony label: it is Luo's finite-difference commutator kernel r_p,
-- its low/high projector split, and the three resulting flux pieces.  The
-- repository's already-constructed Hermitian projectors, Parseval transport,
-- cutoff-indexed geometry, operator gap and residue-scale authority are inputs
-- to later consumers and are not reconstructed here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record LuoExactFluxKernelDecomposition
    {stateLevel tensorLevel scalarLevel : Level}
    (State : Set stateLevel)
    (Tensor : Set tensorLevel)
    (Scalar : Set scalarLevel)
    : Set (lsuc (stateLevel ⊔ tensorLevel ⊔ scalarLevel)) where
  field
    lowPass highPass : Nat → State → State
    tensor : State → State → Tensor
    addTensor subtractTensor : Tensor → Tensor → Tensor

    projectedTensor : Nat → State → Tensor

    -- Literal Constantin--E--Titi/Luo increment kernel
    incrementKernel : Nat → State → Tensor
    lowIncrementKernel highIncrementKernel : Nat → State → Tensor

    incrementKernelSplit :
      (shell : Nat) → (u : State) →
      incrementKernel shell u
      ≡ addTensor
          (lowIncrementKernel shell u)
          (highIncrementKernel shell u)

    -- Δ_{≤p}(u⊗u)
    --   = r_p(u,u) - u_{>p}⊗u_{>p} + u_{≤p}⊗u_{≤p}.
    luoProjectedTensorIdentity :
      (shell : Nat) → (u : State) →
      projectedTensor shell u
      ≡ addTensor
          (subtractTensor
            (incrementKernel shell u)
            (tensor (highPass shell u) (highPass shell u)))
          (tensor (lowPass shell u) (lowPass shell u))

    absoluteFlux : Nat → State → Scalar
    fluxPiece1 fluxPiece2 fluxPiece3 : Nat → State → Scalar
    addScalar : Scalar → Scalar → Scalar

    fluxThreePieceIdentity :
      (shell : Nat) → (u : State) →
      absoluteFlux shell u
      ≡ addScalar
          (addScalar
            (fluxPiece1 shell u)
            (fluxPiece2 shell u))
          (fluxPiece3 shell u)

    lowShellEnergy highShellEnergy lowGradientInfinity :
      Nat → State → Scalar
    multiply : Scalar → Scalar → Scalar
    lessOrEqual : Scalar → Scalar → Set scalarLevel

    -- Source-shaped bounds corresponding to r_{p,1}, r_{p,2}, and u_{>p}².
    fluxPiece1Bound :
      (shell : Nat) → (u : State) →
      lessOrEqual
        (fluxPiece1 shell u)
        (multiply
          (lowShellEnergy shell u)
          (lowGradientInfinity shell u))

    fluxPiece2Bound :
      (shell : Nat) → (u : State) →
      lessOrEqual
        (fluxPiece2 shell u)
        (multiply
          (highShellEnergy shell u)
          (lowGradientInfinity shell u))

    fluxPiece3Bound :
      (shell : Nat) → (u : State) →
      lessOrEqual
        (fluxPiece3 shell u)
        (multiply
          (highShellEnergy shell u)
          (lowGradientInfinity shell u))

open LuoExactFluxKernelDecomposition public

record LuoFluxKernelToWeightedSchur
    {stateLevel tensorLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {Scalar : Set scalarLevel}
    (source : LuoExactFluxKernelDecomposition State Tensor Scalar)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    weightedShellEnergy : Nat → State → Scalar
    schurConstant : Scalar

    sourceEnergySum : Nat → State → Scalar
    sourceEnergySumMeaning :
      (shell : Nat) → (u : State) →
      sourceEnergySum shell u
      ≡ addScalar source
          (lowShellEnergy source shell u)
          (highShellEnergy source shell u)

    weightedSchurDominatesSourceEnergy :
      (shell : Nat) → (u : State) →
      lessOrEqual source
        (sourceEnergySum shell u)
        (multiply source
          schurConstant
          (weightedShellEnergy shell u))

    physicalFluxDominatedByWeightedSchur :
      (shell : Nat) → (u : State) →
      lessOrEqual source
        (absoluteFlux source shell u)
        (multiply source
          (multiply source
            schurConstant
            (weightedShellEnergy shell u))
          (lowGradientInfinity source shell u))

open LuoFluxKernelToWeightedSchur public

luoExactIncrementKernelTargetConstructed : Bool
luoExactIncrementKernelTargetConstructed = true

luoThreePieceFluxTargetConstructed : Bool
luoThreePieceFluxTargetConstructed = true

luoExactFluxKernelPhysicallyInhabited : Bool
luoExactFluxKernelPhysicallyInhabited = false

luoExactIncrementKernelTargetConstructedIsTrue :
  luoExactIncrementKernelTargetConstructed ≡ true
luoExactIncrementKernelTargetConstructedIsTrue = refl

luoThreePieceFluxTargetConstructedIsTrue :
  luoThreePieceFluxTargetConstructed ≡ true
luoThreePieceFluxTargetConstructedIsTrue = refl

luoExactFluxKernelPhysicallyInhabitedIsFalse :
  luoExactFluxKernelPhysicallyInhabited ≡ false
luoExactFluxKernelPhysicallyInhabitedIsFalse = refl
