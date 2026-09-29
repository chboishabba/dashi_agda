{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Exact as R557
open import DASHI.Physics.YangMills.CompactLieProofLevel

continuumCovarianceCompilerMachineChecked :
  R557.round557FiniteToContinuumCovarianceCompilerLevel ≡ machineChecked
continuumCovarianceCompilerMachineChecked = refl

massGapCompilerMachineChecked :
  R557.round557MassGapCompilerLevel ≡ machineChecked
massGapCompilerMachineChecked = refl

noSeparateContinuumWilsonConvergencePayment :
  R557.separateContinuumWilsonConvergencePaymentRequired ≡ false
noSeparateContinuumWilsonConvergencePayment = refl

noPrintedJRoute :
  R557.printedJRouteRequired ≡ false
noPrintedJRoute = refl
