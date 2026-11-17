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

fleetTargetStill58 :
  Manifest.fleetRecordedFormalGapCount ≡ 58
fleetTargetStill58 = Manifest.fleetRecordedFormalGapCountIs58

dischargedStill584 :
  Manifest.fleetRecordedDischargedCount ≡ 584
dischargedStill584 = Manifest.fleetRecordedDischargedCountIs584

contradictionsStill44 :
  Manifest.fleetRecordedContradictionCount ≡ 44
contradictionsStill44 = Manifest.fleetRecordedContradictionCountIs44

esdStillReadOnly :
  Manifest.esdSurfaceEdited ≡ false
esdStillReadOnly = refl
