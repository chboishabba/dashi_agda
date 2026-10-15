module DASHI.Physics.Chemistry.AmmoniaMonster3BActionProbeExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Monster3B
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- WHAT CAN ACTUALLY BE SHARED BETWEEN NH3 AND MONSTER-3B?
--
-- Both lanes already have a genuine C3 character coordinate.  We therefore
-- construct the exact phase-coordinate map.  This is the strongest sound
-- intertwiner presently available: it identifies the restriction coordinate,
-- NOT the molecular state space with a Monster module and NOT a Monster action
-- on NH3.
------------------------------------------------------------------------

ammoniaPhaseToMonsterPhase :
  NH3.ElectronicC3Phase → Monster3B.CentralPhase3
ammoniaPhaseToMonsterPhase NH3.invariant = Monster3B.phaseOne
ammoniaPhaseToMonsterPhase NH3.zeta = Monster3B.phaseZeta
ammoniaPhaseToMonsterPhase NH3.zetaSquared = Monster3B.phaseZetaSquared

monsterPhaseToAmmoniaPhase :
  Monster3B.CentralPhase3 → NH3.ElectronicC3Phase
monsterPhaseToAmmoniaPhase Monster3B.phaseOne = NH3.invariant
monsterPhaseToAmmoniaPhase Monster3B.phaseZeta = NH3.zeta
monsterPhaseToAmmoniaPhase Monster3B.phaseZetaSquared = NH3.zetaSquared

phaseRoundTripNH3 :
  (phase : NH3.ElectronicC3Phase) →
  monsterPhaseToAmmoniaPhase (ammoniaPhaseToMonsterPhase phase) ≡ phase
phaseRoundTripNH3 NH3.invariant = refl
phaseRoundTripNH3 NH3.zeta = refl
phaseRoundTripNH3 NH3.zetaSquared = refl

phaseRoundTripMonster :
  (phase : Monster3B.CentralPhase3) →
  ammoniaPhaseToMonsterPhase (monsterPhaseToAmmoniaPhase phase) ≡ phase
phaseRoundTripMonster Monster3B.phaseOne = refl
phaseRoundTripMonster Monster3B.phaseZeta = refl
phaseRoundTripMonster Monster3B.phaseZetaSquared = refl

ammoniaFourierRow : NH3.ElectronicC3Phase → Fourier.FourierRow
ammoniaFourierRow = NH3.phaseFourierRow

record C3PhaseCoordinateIntertwiner : Set where
  constructor c3PhaseCoordinateIntertwiner
  field
    forward : NH3.ElectronicC3Phase → Monster3B.CentralPhase3
    backward : Monster3B.CentralPhase3 → NH3.ElectronicC3Phase
    nh3RoundTrip :
      (x : NH3.ElectronicC3Phase) → backward (forward x) ≡ x
    monsterRoundTrip :
      (x : Monster3B.CentralPhase3) → forward (backward x) ≡ x
    scope : String

open C3PhaseCoordinateIntertwiner public

canonicalC3PhaseCoordinateIntertwiner : C3PhaseCoordinateIntertwiner
canonicalC3PhaseCoordinateIntertwiner =
  c3PhaseCoordinateIntertwiner
    ammoniaPhaseToMonsterPhase
    monsterPhaseToAmmoniaPhase
    phaseRoundTripNH3
    phaseRoundTripMonster
    "exact identification of the abstract C3 phase coordinate only; no map between NH3 electronic states and the Monster VOA/3B representation carrier"

------------------------------------------------------------------------
-- The attempted promotion therefore stops exactly where it should: a Monster
-- action would require a state map into a literal Monster representation and
-- equivariance under the Monster action, not just the common C3 quotient.
------------------------------------------------------------------------

record AmmoniaMonsterProbeBoundary : Set where
  constructor ammoniaMonsterProbeBoundary
  field
    c3PhaseCoordinateMapPaid : Bool
    c3PhaseCoordinateMapPaidIsTrue : c3PhaseCoordinateMapPaid ≡ true
    sharedC3CharacterCoordinatePaid : Bool
    sharedC3CharacterCoordinatePaidIsTrue : sharedC3CharacterCoordinatePaid ≡ true
    monsterActionOnAmmoniaPaid : Bool
    monsterActionOnAmmoniaPaidIsFalse : monsterActionOnAmmoniaPaid ≡ false
    sameObjectMonsterIntertwinerPaid : Bool
    sameObjectMonsterIntertwinerPaidIsFalse : sameObjectMonsterIntertwinerPaid ≡ false
    phaseCoordinateEqualityCreatesMonsterModule : Bool
    phaseCoordinateEqualityCreatesMonsterModuleIsFalse :
      phaseCoordinateEqualityCreatesMonsterModule ≡ false
    c3RestrictionExtendsUniquelyToMonster : Bool
    c3RestrictionExtendsUniquelyToMonsterIsFalse :
      c3RestrictionExtendsUniquelyToMonster ≡ false
    missingStateSpaceMap : String
    missingEquivarianceLaw : String

open AmmoniaMonsterProbeBoundary public

canonicalAmmoniaMonsterProbeBoundary : AmmoniaMonsterProbeBoundary
canonicalAmmoniaMonsterProbeBoundary =
  ammoniaMonsterProbeBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "construct NH3 electronic/vibronic State -> literal Monster/VOA State on the SAME claimed physical object"
    "prove phi(g·psi) = g·phi(psi) for the promoted action, then show the action has physical rather than merely coordinate authority"
