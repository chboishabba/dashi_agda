{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalCylinderRepresentationRound499Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsPhysicalCylinderRepresentationRound499Exact as R499
open import DASHI.Physics.YangMills.CompactLieProofLevel

physicalRepresentationCompilerMachineChecked :
  R499.round499PhysicalRepresentationCompilerLevel ≡ machineChecked
physicalRepresentationCompilerMachineChecked = refl

finitePremeasureAssemblyMachineChecked :
  R499.round499FinitePremeasureAssemblyLevel ≡ machineChecked
finitePremeasureAssemblyMachineChecked = refl

projectivePremeasureAssemblyMachineChecked :
  R499.round499ProjectivePremeasureAssemblyLevel ≡ machineChecked
projectivePremeasureAssemblyMachineChecked = refl
