module DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- SOURCE / AUTHORITY BOUNDARY
--
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted here.
--
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted here.
--
-- The papers motivate Fourier/phase representations for modular arithmetic.
-- The theorem below is an abstract character-homomorphism interface plus a
-- concrete C3 instance.  It does not claim every neural representation is a
-- group character and deliberately generalizes beyond the repository's C3.
------------------------------------------------------------------------

nandaProgressTitle : String
nandaProgressTitle = "Progress measures for grokking via mechanistic interpretability"

gromovModularTitle : String
gromovModularTitle = "Grokking modular arithmetic"

record TaskCharacterHomomorphism (Task Phase : Set) : Set₁ where
  constructor taskCharacterHomomorphism
  field
    taskCompose : Task → Task → Task
    phaseCompose : Phase → Phase → Phase
    character : Task → Phase
    characterPreservesComposition :
      (left right : Task) →
      character (taskCompose left right)
      ≡ phaseCompose (character left) (character right)

open TaskCharacterHomomorphism public

------------------------------------------------------------------------
-- Concrete C3 task/phase character.
------------------------------------------------------------------------

phaseComposeC3 :
  Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Wheel.DepthWheelPhase
phaseComposeC3 Wheel.phase-0 right = right
phaseComposeC3 Wheel.phase-1 Wheel.phase-0 = Wheel.phase-1
phaseComposeC3 Wheel.phase-1 Wheel.phase-1 = Wheel.phase-2
phaseComposeC3 Wheel.phase-1 Wheel.phase-2 = Wheel.phase-0
phaseComposeC3 Wheel.phase-2 Wheel.phase-0 = Wheel.phase-2
phaseComposeC3 Wheel.phase-2 Wheel.phase-1 = Wheel.phase-0
phaseComposeC3 Wheel.phase-2 Wheel.phase-2 = Wheel.phase-1

c3CharacterModel :
  TaskCharacterHomomorphism Wheel.DepthWheelPhase Wheel.DepthWheelPhase
c3CharacterModel =
  taskCharacterHomomorphism
    phaseComposeC3
    phaseComposeC3
    (λ phase → phase)
    preserve
  where
    preserve :
      (left right : Wheel.DepthWheelPhase) →
      phaseComposeC3 left right ≡ phaseComposeC3 left right
    preserve left right = refl

phaseOnePlusPhaseOneIsPhaseTwo :
  taskCompose c3CharacterModel Wheel.phase-1 Wheel.phase-1 ≡ Wheel.phase-2
phaseOnePlusPhaseOneIsPhaseTwo = refl

phaseOnePlusPhaseTwoWrapsToZero :
  taskCompose c3CharacterModel Wheel.phase-1 Wheel.phase-2 ≡ Wheel.phase-0
phaseOnePlusPhaseTwoWrapsToZero = refl

phaseTwoPlusPhaseTwoWrapsToOne :
  taskCompose c3CharacterModel Wheel.phase-2 Wheel.phase-2 ≡ Wheel.phase-1
phaseTwoPlusPhaseTwoWrapsToOne = refl

c3CharacterCompositionExact :
  (left right : Wheel.DepthWheelPhase) →
  character c3CharacterModel (taskCompose c3CharacterModel left right)
  ≡ phaseCompose c3CharacterModel
      (character c3CharacterModel left)
      (character c3CharacterModel right)
c3CharacterCompositionExact = characterPreservesComposition c3CharacterModel

------------------------------------------------------------------------
-- The generic carrier is the anti-numerology theorem surface: downstream
-- neural/phased-lattice consumers must supply the task symmetry and its
-- character law.  C3 is only one concrete specialization.
------------------------------------------------------------------------
