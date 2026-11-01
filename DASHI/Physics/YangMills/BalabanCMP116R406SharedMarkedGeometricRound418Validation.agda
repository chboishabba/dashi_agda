{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Exact as R418
open import DASHI.Physics.YangMills.CompactLieProofLevel

r406SharedMarkedCompilerMachineChecked :
  R418.round418R406SharedMarkedGeometricCompilerLevel ≡ machineChecked
r406SharedMarkedCompilerMachineChecked = refl

perDomainAmplitudeNotMandatory :
  R418.round418PerDomainAmplitudeDecompositionMandatory ≡ false
perDomainAmplitudeNotMandatory = refl
