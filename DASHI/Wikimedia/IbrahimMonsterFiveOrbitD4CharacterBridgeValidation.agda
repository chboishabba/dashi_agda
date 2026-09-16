module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4CharacterBridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4CharacterBridgeExact as B

pythonProbeSourceRegression :
  B.pythonCharacterProbeSourceWritten B.currentFiveOrbitD4CharacterBoundary ≡ true
pythonProbeSourceRegression = refl

characterRegression :
  B.permutationCharacterFiveFiveOneThreeThreeRetained B.currentFiveOrbitD4CharacterBoundary ≡ true
characterRegression = refl

quotientDecompositionRegression :
  B.quotientDecompositionThreeA1B1B2Retained B.currentFiveOrbitD4CharacterBoundary ≡ true
quotientDecompositionRegression = refl

removedERegression :
  B.rawNineToQuotientRemovesTwoECopies B.currentFiveOrbitD4CharacterBoundary ≡ true
removedERegression = refl

oneToOneFirewallRegression :
  B.fiveOrbitsAreFiveIrrepsOneToOne B.currentFiveOrbitD4CharacterBoundary ≡ false
oneToOneFirewallRegression = refl

kernelFirewallRegression :
  B.agdaKernelCharacterDecompositionObserved B.currentFiveOrbitD4CharacterBoundary ≡ false
kernelFirewallRegression = refl

monsterFirewallRegression :
  B.characterBridgeCreatesMonster42dAction B.currentFiveOrbitD4CharacterBoundary ≡ false
monsterFirewallRegression = refl
