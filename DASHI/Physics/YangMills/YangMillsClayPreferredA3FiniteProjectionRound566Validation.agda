{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteProjectionRound566Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteProjectionRound566Exact as R566
open import DASHI.Physics.YangMills.CompactLieProofLevel

fivePhysicalA3Subclaims :
  R566.a3OpenPhysicalSubclaimCount ≡ 5
fivePhysicalA3Subclaims = refl

finiteProjectionCompilerOwned :
  R566.a3FiniteProjectionToCylinderCompilerLevel ≡ machineChecked
finiteProjectionCompilerOwned = refl

limitIntegralCompilerOwned :
  R566.a3SelectedLimitIntegralCompilerLevel ≡ machineChecked
limitIntegralCompilerOwned = refl

noArbitraryObservables :
  R566.arbitraryObservableRepresentationRequired ≡ false
noArbitraryObservables = refl

noProkhorov :
  R566.prokhorovRequired ≡ false
noProkhorov = refl
