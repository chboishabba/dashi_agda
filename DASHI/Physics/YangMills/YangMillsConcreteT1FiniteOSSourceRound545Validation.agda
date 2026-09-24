{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as R545
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R545.round545T1FiniteOSSourceCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

bosonicCannotDriftFamilies :
  R545.round545BosonicMayUseDifferentFiniteFamily ≡ false
bosonicCannotDriftFamilies = refl

euclideanNotIndependent :
  R545.round545IndependentFiniteEuclideanApplicationRequired ≡ false
euclideanNotIndependent = refl

wilsonRPNotIndependent :
  R545.round545IndependentFiniteWilsonRPApplicationRequired ≡ false
wilsonRPNotIndependent = refl
