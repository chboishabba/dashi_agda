{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalCanonicalR406Round421Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116PhysicalCanonicalR406Round421Exact as R421
open import DASHI.Physics.YangMills.CompactLieProofLevel

physicalCanonicalR406CompilerMachineChecked :
  R421.round421PhysicalCanonicalR406CompilerLevel ≡ machineChecked
physicalCanonicalR406CompilerMachineChecked = refl

independentPhysicalCoordinateWeldsPruned :
  R421.round421IndependentPhysicalCoordinateWeldsRequired ≡ false
independentPhysicalCoordinateWeldsPruned = refl

noAdditionalDecayTheorem :
  R421.round421AdditionalDecayTheoremRequired ≡ false
noAdditionalDecayTheorem = refl
