{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CoreClusteringAttachmentRound429Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5CoreClusteringAttachmentRound429Exact as R429
open import DASHI.Physics.YangMills.CompactLieProofLevel

clusteringAttachmentCompilerMachineChecked :
  R429.round429ClusteringAttachmentCompilerLevel ≡ machineChecked
clusteringAttachmentCompilerMachineChecked = refl

independentH2ClusteringPruned :
  R429.round429IndependentH2ClusteringInputRequired ≡ false
independentH2ClusteringPruned = refl


coreConstructionDoesNotRequireClustering :
  R429.round429ClusteringRequiredForCoreConstruction ≡ false
coreConstructionDoesNotRequireClustering = refl
