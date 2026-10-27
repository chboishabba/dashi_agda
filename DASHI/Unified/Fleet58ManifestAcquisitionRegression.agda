{-# OPTIONS --safe #-}
module DASHI.Unified.Fleet58ManifestAcquisitionRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.Fleet58ManifestAcquisitionExact as Manifest

manifestStillMissing :
  Manifest.named58ManifestAcquired ≡ false
manifestStillMissing = refl

perGapDispatchStillBlocked :
  Manifest.perGapDispatchEnabled ≡ false
perGapDispatchStillBlocked = refl

acquisitionRouteBound :
  Manifest.manifestAcquisitionRouteBound ≡ true
acquisitionRouteBound = refl

relatedSearchRequired :
  Manifest.relatedSymbolsRequired ≡ true
relatedSearchRequired = refl

discoverRequired :
  Manifest.discoverRequired ≡ true
discoverRequired = refl

roundLineageRequired :
  Manifest.roundLineageRequired ≡ true
roundLineageRequired = refl

searchPriorityStillNotProof :
  Manifest.searchPriorityCreatesProof ≡ false
searchPriorityStillNotProof = refl

esdStillReadOnly :
  Manifest.esdSurfaceEdited ≡ false
esdStillReadOnly = refl
