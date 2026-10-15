module DASHI.Physics.Chemistry.AmmoniaGroundStateC3ActionExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as E
import DASHI.Physics.Chemistry.AmmoniaHamiltonianWavefunctionExact as W

phaseMul : E.ElectronicC3Phase → E.ElectronicC3Phase → E.ElectronicC3Phase
phaseMul E.invariant x = x
phaseMul x E.invariant = x
phaseMul E.zeta E.zeta = E.zetaSquared
phaseMul E.zeta E.zetaSquared = E.invariant
phaseMul E.zetaSquared E.zeta = E.invariant
phaseMul E.zetaSquared E.zetaSquared = E.zeta

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

occupiedEManifoldPhase : E.ElectronicC3Phase
occupiedEManifoldPhase =
  phaseMul
    (phaseMul E.zeta E.zeta)
    (phaseMul E.zetaSquared E.zetaSquared)

groundDeterminantPhase : E.ElectronicC3Phase
groundDeterminantPhase = occupiedEManifoldPhase

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

open GroundStateC3Action public

canonicalGroundStateC3Action : GroundStateC3Action
canonicalGroundStateC3Action =
  groundStateC3Action
    ⊤
    tt
    (λ x → x)
    refl
    groundDeterminantPhase
    refl
    W.canonicalNH3OccupationState

record GroundStateC3Boundary : Set where
  constructor groundStateC3Boundary
  field
    phaseAdaptedOccupiedOrbitalsPaid : Bool
    phaseAdaptedOccupiedOrbitalsPaidIsTrue : phaseAdaptedOccupiedOrbitalsPaid ≡ true
    literalGroundConfigurationC3ActionPaid : Bool
    literalGroundConfigurationC3ActionPaidIsTrue :
      literalGroundConfigurationC3ActionPaid ≡ true
    closedShellDeterminantInvariantPaid : Bool
    closedShellDeterminantInvariantPaidIsTrue :
      closedShellDeterminantInvariantPaid ≡ true
    realSpaceWavefunctionActionPaid : Bool
    realSpaceWavefunctionActionPaidIsFalse : realSpaceWavefunctionActionPaid ≡ false
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
    false refl
    false refl
    false refl
