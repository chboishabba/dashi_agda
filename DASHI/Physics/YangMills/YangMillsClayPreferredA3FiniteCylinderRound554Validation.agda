{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteCylinderRound554Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteCylinderRound554Exact as R554
open import DASHI.Physics.YangMills.CompactLieProofLevel

a3OpenSubclaimsRemainFive :
  R554.a3PreferredOpenPhysicalSubclaimCount ≡ 5
a3OpenSubclaimsRemainFive = refl

selectedLimitIntegralIsCompilerOwned :
  R554.a3SelectedLimitIntegralEqualityCompilerLevel ≡ machineChecked
selectedLimitIntegralIsCompilerOwned = refl

finiteSelectedConvergenceCompilerOwned :
  R554.a3FiniteSelectedConvergenceCompilerLevel ≡ machineChecked
finiteSelectedConvergenceCompilerOwned = refl

noProkhorov :
  R554.prokhorovRequired ≡ false
noProkhorov = refl

noArbitraryObservableRepresentation :
  R554.arbitraryObservableRepresentationRequired ≡ false
noArbitraryObservableRepresentation = refl
