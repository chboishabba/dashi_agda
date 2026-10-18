{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealR415ClusteringValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealR415ClusteringExact as R417
open import DASHI.Physics.YangMills.CompactLieProofLevel

r415ToContinuumCompilerIsMachineChecked :
  R417.r415ToContinuumPhysicalClusteringCompilerLevel ≡ machineChecked
r415ToContinuumCompilerIsMachineChecked = refl
