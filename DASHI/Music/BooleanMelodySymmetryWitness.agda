module DASHI.Music.BooleanMelodySymmetryWitness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Music.MusicalSymmetryDynamicsCore as Core

------------------------------------------------------------------------
-- Exact four-state witness.
--
-- A two-position binary melody is enough to prove the structural point:
-- swap symmetry has two fixed melodies; copying the left pitch to the right
-- is an idempotent repair; every state reaches a symmetric fixed point; and
-- the two fixed points each have basin volume two.
------------------------------------------------------------------------

data Melody₂ : Set where
  m00 : Melody₂
  m01 : Melody₂
  m10 : Melody₂
  m11 : Melody₂

swap : Melody₂ → Melody₂
swap m00 = m00
swap m01 = m10
swap m10 = m01
swap m11 = m11

swapInvolutive : ∀ melody → swap (swap melody) ≡ melody
swapInvolutive m00 = refl
swapInvolutive m01 = refl
swapInvolutive m10 = refl
swapInvolutive m11 = refl

twoBitSymmetry : Core.InvolutiveSymmetry Melody₂
twoBitSymmetry =
  record
    { symmetry = swap
    ; involutive = swapInvolutive
    }

data Defect : Set where
  defect0 : Defect
  defect1 : Defect

infix 4 _≤ᴰ_

data _≤ᴰ_ : Defect → Defect → Set where
  defect0≤defect0 : defect0 ≤ᴰ defect0
  defect0≤defect1 : defect0 ≤ᴰ defect1
  defect1≤defect1 : defect1 ≤ᴰ defect1

asymmetryDefect : Melody₂ → Defect
asymmetryDefect m00 = defect0
asymmetryDefect m01 = defect1
asymmetryDefect m10 = defect1
asymmetryDefect m11 = defect0

symmetricHasZeroDefect :
  ∀ {melody} →
  Core.Symmetric twoBitSymmetry melody →
  asymmetryDefect melody ≡ defect0
symmetricHasZeroDefect {m00} _ = refl
symmetricHasZeroDefect {m01} ()
symmetricHasZeroDefect {m10} ()
symmetricHasZeroDefect {m11} _ = refl

zeroDefectIsSymmetric :
  ∀ {melody} →
  asymmetryDefect melody ≡ defect0 →
  Core.Symmetric twoBitSymmetry melody
zeroDefectIsSymmetric {m00} _ = refl
zeroDefectIsSymmetric {m01} ()
zeroDefectIsSymmetric {m10} ()
zeroDefectIsSymmetric {m11} _ = refl

twoBitEnergy :
  Core.AsymmetryEnergy Melody₂ twoBitSymmetry
twoBitEnergy =
  record
    { Energy = Defect
    ; zeroEnergy = defect0
    ; energyOrder = _≤ᴰ_
    ; energy = asymmetryDefect
    ; symmetricHasZeroEnergy = symmetricHasZeroDefect
    ; zeroEnergyIsSymmetric = zeroDefectIsSymmetric
    }

copyLeftRepair : Melody₂ → Melody₂
copyLeftRepair m00 = m00
copyLeftRepair m01 = m00
copyLeftRepair m10 = m11
copyLeftRepair m11 = m11

copyLeftRepairIsSymmetric :
  ∀ melody →
  Core.Symmetric twoBitSymmetry (copyLeftRepair melody)
copyLeftRepairIsSymmetric m00 = refl
copyLeftRepairIsSymmetric m01 = refl
copyLeftRepairIsSymmetric m10 = refl
copyLeftRepairIsSymmetric m11 = refl

copyLeftFixesSymmetric :
  ∀ {melody} →
  Core.Symmetric twoBitSymmetry melody →
  copyLeftRepair melody ≡ melody
copyLeftFixesSymmetric {m00} _ = refl
copyLeftFixesSymmetric {m01} ()
copyLeftFixesSymmetric {m10} ()
copyLeftFixesSymmetric {m11} _ = refl

copyLeftEnergyDoesNotIncrease :
  ∀ melody →
  asymmetryDefect (copyLeftRepair melody) ≤ᴰ asymmetryDefect melody
copyLeftEnergyDoesNotIncrease m00 = defect0≤defect0
copyLeftEnergyDoesNotIncrease m01 = defect0≤defect1
copyLeftEnergyDoesNotIncrease m10 = defect0≤defect1
copyLeftEnergyDoesNotIncrease m11 = defect0≤defect0

twoBitRepair :
  Core.SymmetryRepair Melody₂ twoBitSymmetry twoBitEnergy
twoBitRepair =
  record
    { repair = copyLeftRepair
    ; repairedIsSymmetric = copyLeftRepairIsSymmetric
    ; fixesSymmetric = copyLeftFixesSymmetric
    ; energyDoesNotIncrease = copyLeftEnergyDoesNotIncrease
    }

copyLeftRepairIdempotent :
  ∀ melody →
  copyLeftRepair (copyLeftRepair melody) ≡ copyLeftRepair melody
copyLeftRepairIdempotent =
  Core.repairIdempotent twoBitRepair

copyLeftFixedPointIsSymmetric :
  ∀ {melody} →
  copyLeftRepair melody ≡ melody →
  Core.Symmetric twoBitSymmetry melody
copyLeftFixedPointIsSymmetric =
  Core.fixedRepairIsSymmetric twoBitRepair

copyLeftRepairEnergyIsZero :
  ∀ melody →
  asymmetryDefect (copyLeftRepair melody) ≡ defect0
copyLeftRepairEnergyIsZero m00 = refl
copyLeftRepairEnergyIsZero m01 = refl
copyLeftRepairEnergyIsZero m10 = refl
copyLeftRepairEnergyIsZero m11 = refl

m01IsNotARepairFixedPoint :
  copyLeftRepair m01 ≡ m01 →
  ⊥
m01IsNotARepairFixedPoint ()

m10IsNotARepairFixedPoint :
  copyLeftRepair m10 ≡ m10 →
  ⊥
m10IsNotARepairFixedPoint ()

------------------------------------------------------------------------
-- Exact basin partition.
------------------------------------------------------------------------

data SymmetricAttractor₂ : Set where
  lowAttractor : SymmetricAttractor₂
  highAttractor : SymmetricAttractor₂

attractorOf : Melody₂ → SymmetricAttractor₂
attractorOf m00 = lowAttractor
attractorOf m01 = lowAttractor
attractorOf m10 = highAttractor
attractorOf m11 = highAttractor

realizeAttractor : SymmetricAttractor₂ → Melody₂
realizeAttractor lowAttractor = m00
realizeAttractor highAttractor = m11

realizedAttractorIsFixed :
  ∀ attractor →
  attractorOf (realizeAttractor attractor) ≡ attractor
realizedAttractorIsFixed lowAttractor = refl
realizedAttractorIsFixed highAttractor = refl

twoBitAttractorAssignment :
  Core.AttractorAssignment Melody₂ SymmetricAttractor₂
twoBitAttractorAssignment =
  record
    { attractorOf = attractorOf
    ; realize = realizeAttractor
    ; realizedAttractorIsFixed = realizedAttractorIsFixed
    }

repairRealizesAssignedAttractor :
  ∀ melody →
  copyLeftRepair melody ≡ realizeAttractor (attractorOf melody)
repairRealizesAssignedAttractor m00 = refl
repairRealizesAssignedAttractor m01 = refl
repairRealizesAssignedAttractor m10 = refl
repairRealizesAssignedAttractor m11 = refl

basinVolume : SymmetricAttractor₂ → Nat
basinVolume lowAttractor = 2
basinVolume highAttractor = 2

twoBitBasinMeasurement :
  Core.FiniteBasinMeasurement SymmetricAttractor₂
twoBitBasinMeasurement =
  record
    { basinVolume = basinVolume
    ; measuredStateCount = 4
    }

lowBasinVolumeIsTwo : basinVolume lowAttractor ≡ 2
lowBasinVolumeIsTwo = refl

highBasinVolumeIsTwo : basinVolume highAttractor ≡ 2
highBasinVolumeIsTwo = refl

allFourStatesAccountedFor :
  basinVolume lowAttractor + basinVolume highAttractor ≡ 4
allFourStatesAccountedFor = refl
