module DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as E
import DASHI.Physics.Chemistry.AmmoniaHamiltonianWavefunctionExact as W

phaseMul : E.ElectronicC3Phase → E.ElectronicC3Phase → E.ElectronicC3Phase
phaseMul E.invariant E.invariant = E.invariant
phaseMul E.invariant E.zeta = E.zeta
phaseMul E.invariant E.zetaSquared = E.zetaSquared
phaseMul E.zeta E.invariant = E.zeta
phaseMul E.zeta E.zeta = E.zetaSquared
phaseMul E.zeta E.zetaSquared = E.invariant
phaseMul E.zetaSquared E.invariant = E.zetaSquared
phaseMul E.zetaSquared E.zeta = E.invariant
phaseMul E.zetaSquared E.zetaSquared = E.zeta

------------------------------------------------------------------------
-- Phase-adapted interpretation of the named E-pair carrier.
--
-- The historical oneEX/oneEY constructor names are retained for branch/API
-- stability, but in this module they are explicitly interpreted as the two
-- complex C3 eigen-combinations of the E doublet, with phases zeta/zeta^2.
------------------------------------------------------------------------

spinOrbitalPhase : W.NH3OccupiedSpinOrbital → E.ElectronicC3Phase
spinOrbitalPhase W.oneA1Alpha = E.invariant
spinOrbitalPhase W.oneA1Beta = E.invariant
spinOrbitalPhase W.twoA1Alpha = E.invariant
spinOrbitalPhase W.twoA1Beta = E.invariant
spinOrbitalPhase W.oneEXAlpha = E.zeta
spinOrbitalPhase W.oneEXBeta = E.zeta
spinOrbitalPhase W.oneEYAlpha = E.zetaSquared
spinOrbitalPhase W.oneEYBeta = E.zetaSquared
spinOrbitalPhase W.threeA1Alpha = E.invariant
spinOrbitalPhase W.threeA1Beta = E.invariant

foldOccupiedPhase : List W.NH3OccupiedSpinOrbital → E.ElectronicC3Phase
foldOccupiedPhase [] = E.invariant
foldOccupiedPhase (orbital ∷ rest) =
  phaseMul (spinOrbitalPhase orbital) (foldOccupiedPhase rest)

groundDeterminantPhase : E.ElectronicC3Phase
groundDeterminantPhase = foldOccupiedPhase W.canonicalOccupiedSpinOrbitals

groundDeterminantPhaseInvariant : groundDeterminantPhase ≡ E.invariant
groundDeterminantPhaseInvariant = refl

------------------------------------------------------------------------
-- The 1A1 closed-shell ground configuration itself carries the trivial C3
-- representation.  This is NOT a real-space wavefunction action: the latter
-- still needs numerical/spatial orbitals and an operator action on that space.
------------------------------------------------------------------------

data CanonicalGroundConfiguration : Set where
  canonicalGroundConfiguration : CanonicalGroundConfiguration

canonicalGroundGenerator :
  CanonicalGroundConfiguration → CanonicalGroundConfiguration
canonicalGroundGenerator canonicalGroundConfiguration = canonicalGroundConfiguration

record GroundStateC3Action : Set where
  constructor groundStateC3Action
  field
    State : Set
    state : State
    generator : State → State
    generatorCubed : generator (generator (generator state)) ≡ state
    determinantPhase : E.ElectronicC3Phase
    determinantPhaseInvariant : determinantPhase ≡ E.invariant
    occupationState : W.NH3OccupationState
    scope : String

open GroundStateC3Action public

canonicalGroundStateC3Action : GroundStateC3Action
canonicalGroundStateC3Action =
  groundStateC3Action
    CanonicalGroundConfiguration
    canonicalGroundConfiguration
    canonicalGroundGenerator
    refl
    groundDeterminantPhase
    groundDeterminantPhaseInvariant
    W.canonicalNH3OccupationState
    "trivial C3 representation of the selected 1A1 closed-shell configuration; does not constitute a real-space molecular wavefunction action"

record GroundStateC3Boundary : Set where
  constructor groundStateC3Boundary
  field
    phaseAdaptedOccupiedOrbitalInterpretationPaid : Bool
    phaseAdaptedOccupiedOrbitalInterpretationPaidIsTrue :
      phaseAdaptedOccupiedOrbitalInterpretationPaid ≡ true
    determinantPhaseComputedFromOccupiedCarrier : Bool
    determinantPhaseComputedFromOccupiedCarrierIsTrue :
      determinantPhaseComputedFromOccupiedCarrier ≡ true
    trivialGroundConfigurationC3RepresentationPaid : Bool
    trivialGroundConfigurationC3RepresentationPaidIsTrue :
      trivialGroundConfigurationC3RepresentationPaid ≡ true
    closedShellDeterminantInvariantPaid : Bool
    closedShellDeterminantInvariantPaidIsTrue :
      closedShellDeterminantInvariantPaid ≡ true
    nontrivialRealSpaceWavefunctionC3ActionPaid : Bool
    nontrivialRealSpaceWavefunctionC3ActionPaidIsFalse :
      nontrivialRealSpaceWavefunctionC3ActionPaid ≡ false
    excitedElectronicManifoldActionPaid : Bool
    excitedElectronicManifoldActionPaidIsFalse :
      excitedElectronicManifoldActionPaid ≡ false
    c3GroundStateActionCreatesMonsterAction : Bool
    c3GroundStateActionCreatesMonsterActionIsFalse :
      c3GroundStateActionCreatesMonsterAction ≡ false

open GroundStateC3Boundary public

canonicalGroundStateC3Boundary : GroundStateC3Boundary
canonicalGroundStateC3Boundary =
  groundStateC3Boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
