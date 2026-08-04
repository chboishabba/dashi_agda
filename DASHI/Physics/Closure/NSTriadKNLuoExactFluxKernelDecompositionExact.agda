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
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Record the literal nonlinear identity used in Proposition 3.1.  This is not
-- a generic Bony label: it is Luo's finite-difference commutator kernel r_p,
-- its low/high projector split, and the three resulting flux pieces.
--
-- The high-flux sign identity is explicitly grounded in
--
--   integral (u dot grad)u dot u = 0,
--
-- which is available on the interval where the Leray--Hopf solution is already
-- regular and divergence-free.  It is not promoted from the global weak energy
-- inequality alone.
--
-- SOURCE-FIDELITY CORRECTION
-- The physical realization now carries an explicit scalar action on tensors
-- and uses kernelWeight inside the integrand.  The former unweighted formula
-- stored kernelWeight but never applied it, and therefore did not literally
-- represent Luo's r_p integral.
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

    -- Literal Constantin--E--Titi/Luo increment kernel.
    incrementKernel : Nat → State → Tensor
    lowIncrementKernel highIncrementKernel : Nat → State → Tensor

    incrementKernelSplit :
      (shell : Nat) → (u : State) →
      incrementKernel shell u
      ≡ addTensor
          (lowIncrementKernel shell u)
          (highIncrementKernel shell u)

    -- Delta_{<=p}(u tensor u)
    --   = r_p(u,u) - u_{>p} tensor u_{>p}
    --     + u_{<=p} tensor u_{<=p}.
    luoProjectedTensorIdentity :
      (shell : Nat) → (u : State) →
      projectedTensor shell u
      ≡ addTensor
          (subtractTensor
            (incrementKernel shell u)
            (tensor (highPass shell u) (highPass shell u)))
          (tensor (lowPass shell u) (lowPass shell u))

    signedLowFlux signedHighFlux crossFlux : Nat → State → Scalar
    absoluteHighFlux : Nat → State → Scalar
    fluxPiece1 fluxPiece2 fluxPiece3 : Nat → State → Scalar

    zeroScalar : Scalar
    addScalar subtractScalar negateScalar twoTimes : Scalar → Scalar → Scalar
    absoluteValue : Scalar → Scalar

    previousShell : Nat → Nat

    RegularBeforeTerminal : State → Set stateLevel
    DivergenceFree : State → Set stateLevel

    nonlinearFullVelocityPairing : State → Scalar

    divergenceFreeCancellationOnRegularInterval :
      (u : State) →
      RegularBeforeTerminal u →
      DivergenceFree u →
      nonlinearFullVelocityPairing u ≡ zeroScalar

    -- Luo's identity preceding (3.2):
    -- Pi_{>=p} = -Pi_{<=p-1} - 2 cross_p.
    highFluxSignIdentity :
      (shell : Nat) → (u : State) →
      RegularBeforeTerminal u →
      DivergenceFree u →
      signedHighFlux shell u
      ≡ subtractScalar
          (negateScalar zeroScalar
            (signedLowFlux (previousShell shell) u))
          (twoTimes zeroScalar (crossFlux shell u))

    absoluteHighFluxMeaning :
      (shell : Nat) → (u : State) →
      absoluteHighFlux shell u
      ≡ absoluteValue (signedHighFlux shell u)

    fluxThreePieceIdentity :
      (shell : Nat) → (u : State) →
      absoluteHighFlux shell u
      ≡ addScalar
          (addScalar
            (fluxPiece1 shell u)
            (fluxPiece2 shell u))
          (fluxPiece3 shell u)

    lowShellEnergy highShellEnergy lowGradientInfinity :
      Nat → State → Scalar
    multiply : Scalar → Scalar → Scalar
    lessOrEqual : Scalar → Scalar → Set scalarLevel

    -- Source-shaped bounds corresponding to r_{p,1}, r_{p,2}, and u_{>p}^2.
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

record LuoIncrementKernelPhysicalRealization
    {stateLevel tensorLevel scalarLevel spaceLevel : Level}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {Scalar : Set scalarLevel}
    (source : LuoExactFluxKernelDecomposition State Tensor Scalar)
    (Space : Set spaceLevel)
    : Set (lsuc (stateLevel ⊔ tensorLevel ⊔ scalarLevel ⊔ spaceLevel)) where
  field
    translate : Space → State → State
    subtractState : State → State → State
    incrementTensor : State → State → Tensor
    kernelWeight : Nat → Space → Scalar
    scaleTensor : Scalar → Tensor → Tensor
    integrateTensor : (Space → Tensor) → Tensor

    literalIncrementKernelMeaning :
      (shell : Nat) → (u : State) →
      incrementKernel source shell u
      ≡ integrateTensor
          (λ displacement →
            scaleTensor
              (kernelWeight shell displacement)
              (incrementTensor
                (subtractState (translate displacement u) u)
                (subtractState (translate displacement u) u)))

    FourierTerm : Set
    physicalTriadTerms : Nat → State → FourierTerm
    fullShellIncidenceTerms : Nat → State → FourierTerm

    incrementKernelFourierExpansion :
      (shell : Nat) → (u : State) →
      physicalTriadTerms shell u
      ≡ fullShellIncidenceTerms shell u

    lowIncrementPieceMatchesPhysicalTriads : Set
    lowIncrementPieceMatchesPhysicalTriadsWitness :
      lowIncrementPieceMatchesPhysicalTriads

    highIncrementPieceMatchesPhysicalTriads : Set
    highIncrementPieceMatchesPhysicalTriadsWitness :
      highIncrementPieceMatchesPhysicalTriads

    highTailSquareMatchesPhysicalTriads : Set
    highTailSquareMatchesPhysicalTriadsWitness :
      highTailSquareMatchesPhysicalTriads

open LuoIncrementKernelPhysicalRealization public

record LuoFluxKernelToWeightedSchur
    {stateLevel tensorLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {Scalar : Set scalarLevel}
    (source : LuoExactFluxKernelDecomposition State Tensor Scalar)
    : Set (lsuc (stateLevel ⊔ tensorLevel ⊔ scalarLevel)) where
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
        (absoluteHighFlux source shell u)
        (multiply source
          (multiply source
            schurConstant
            (weightedShellEnergy shell u))
          (lowGradientInfinity source shell u))

open LuoFluxKernelToWeightedSchur public

luoExactIncrementKernelTargetConstructed : Bool
luoExactIncrementKernelTargetConstructed = true

luoHighFluxCancellationIdentityRecorded : Bool
luoHighFluxCancellationIdentityRecorded = true

luoThreePieceFluxTargetConstructed : Bool
luoThreePieceFluxTargetConstructed = true

weightedIncrementKernelFormulaCorrected : Bool
weightedIncrementKernelFormulaCorrected = true

luoExactFluxKernelPhysicallyInhabited : Bool
luoExactFluxKernelPhysicallyInhabited = false

luoExactIncrementKernelTargetConstructedIsTrue :
  luoExactIncrementKernelTargetConstructed ≡ true
luoExactIncrementKernelTargetConstructedIsTrue = refl

luoHighFluxCancellationIdentityRecordedIsTrue :
  luoHighFluxCancellationIdentityRecorded ≡ true
luoHighFluxCancellationIdentityRecordedIsTrue = refl

luoThreePieceFluxTargetConstructedIsTrue :
  luoThreePieceFluxTargetConstructed ≡ true
luoThreePieceFluxTargetConstructedIsTrue = refl

weightedIncrementKernelFormulaCorrectedIsTrue :
  weightedIncrementKernelFormulaCorrected ≡ true
weightedIncrementKernelFormulaCorrectedIsTrue = refl

luoExactFluxKernelPhysicallyInhabitedIsFalse :
  luoExactFluxKernelPhysicallyInhabited ≡ false
luoExactFluxKernelPhysicallyInhabitedIsFalse = refl
