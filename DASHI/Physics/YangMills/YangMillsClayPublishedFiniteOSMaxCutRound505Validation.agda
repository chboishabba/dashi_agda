{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMaxCutRound505Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMaxCutRound505Exact as R505
open import DASHI.Physics.YangMills.CompactLieProofLevel

assemblyCompilerMachineChecked :
  R505.round505FiniteOSAssemblyCompilerLevel ≡ machineChecked
assemblyCompilerMachineChecked = refl

euclideanAuthorityStandard :
  R505.round505EuclideanSourceAuthorityLevel ≡ standardImported
euclideanAuthorityStandard = refl

bosonicAuthorityStandard :
  R505.round505BosonicSourceAuthorityLevel ≡ standardImported
bosonicAuthorityStandard = refl
