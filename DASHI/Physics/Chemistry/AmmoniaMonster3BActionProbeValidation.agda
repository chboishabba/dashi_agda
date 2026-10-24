module DASHI.Physics.Chemistry.AmmoniaMonster3BActionProbeValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BActionProbeExact as Probe

phaseCoordinateMapPaid :
  Probe.AmmoniaMonsterProbeBoundary.c3PhaseCoordinateMapPaid
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ true
phaseCoordinateMapPaid = refl

sharedC3CharacterCoordinatePaid :
  Probe.AmmoniaMonsterProbeBoundary.sharedC3CharacterCoordinatePaid
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ true
sharedC3CharacterCoordinatePaid = refl

trivialAnyGroupActionExists :
  Probe.AmmoniaMonsterProbeBoundary.trivialAnyGroupActionOnSingletonAvailable
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ true
trivialAnyGroupActionExists = refl

trivialActionHasNoPhysicalMonsterContent :
  Probe.AmmoniaMonsterProbeBoundary.formalTrivialMonsterActionHasPhysicalContent
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ false
trivialActionHasNoPhysicalMonsterContent = refl

monsterActionStillUnpaid :
  Probe.AmmoniaMonsterProbeBoundary.monsterActionOnAmmoniaPaid
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ false
monsterActionStillUnpaid = refl

monsterIntertwinerStillUnpaid :
  Probe.AmmoniaMonsterProbeBoundary.sameObjectMonsterIntertwinerPaid
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ false
monsterIntertwinerStillUnpaid = refl

phaseMatchDoesNotPromoteMonster :
  Probe.AmmoniaMonsterProbeBoundary.phaseCoordinateEqualityCreatesMonsterModule
    Probe.canonicalAmmoniaMonsterProbeBoundary ≡ false
phaseMatchDoesNotPromoteMonster = refl
