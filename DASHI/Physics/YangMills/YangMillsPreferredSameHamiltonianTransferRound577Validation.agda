{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPreferredSameHamiltonianTransferRound577Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsPreferredSameHamiltonianTransferRound577Exact as R577
open import DASHI.Physics.YangMills.CompactLieProofLevel

sameHamiltonianByConstruction :
  R577.selectedHamiltonianIsReconstructedByConstruction ≡ true
sameHamiltonianByConstruction = refl

noPostHocHamiltonianEquality :
  R577.postHocHamiltonianEqualityRequired ≡ false
noPostHocHamiltonianEquality = refl

noIndependentMassRateCoordinate :
  R577.independentMassRateCoordinateRequired ≡ false
noIndependentMassRateCoordinate = refl

projectionCompilerMachineChecked :
  R577.round577SameHamiltonianProjectionCompilerLevel ≡ machineChecked
projectionCompilerMachineChecked = refl
