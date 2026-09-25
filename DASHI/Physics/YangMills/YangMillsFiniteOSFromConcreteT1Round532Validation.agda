{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Exact as R532
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R532.round532FiniteOSFromT1CompilerLevel ≡ machineChecked
compilerMachineChecked = refl

euclideanNotIndependent :
  R532.round532IndependentEuclideanApplicationRequired ≡ false
euclideanNotIndependent = refl

wilsonRPNotIndependent :
  R532.round532IndependentWilsonRPApplicationRequired ≡ false
wilsonRPNotIndependent = refl
