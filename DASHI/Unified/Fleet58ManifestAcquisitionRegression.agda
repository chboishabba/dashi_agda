{-# OPTIONS --safe #-}
module DASHI.Unified.Fleet58ManifestAcquisitionRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Unified.Fleet58ManifestAcquisitionExact as Manifest
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

manifestStillMissing :
  Manifest.named58ManifestAcquired ≡ false
manifestStillMissing =
  Manifest.named58ManifestAcquiredIsFalse

countStillDoesNotNameRows :
  Manifest.countIdentifiesNamedRows ≡ false
countStillDoesNotNameRows =
  Manifest.countIdentifiesNamedRowsIsFalse

perGapDispatchStillBlocked :
  Manifest.perGapDispatchEnabled ≡ false
perGapDispatchStillBlocked =
  Manifest.perGapDispatchEnabledIsFalse

fleetTargetStill58 :
  Manifest.fleetRecordedFormalGapCount ≡ 58
fleetTargetStill58 =
  Manifest.fleetRecordedFormalGapCountIs58

dischargedStill584 :
  Manifest.fleetRecordedDischargedCount ≡ 584
dischargedStill584 =
  Manifest.fleetRecordedDischargedCountIs584

contradictionsStill44 :
  Manifest.fleetRecordedContradictionCount ≡ 44
contradictionsStill44 =
  Manifest.fleetRecordedContradictionCountIs44

toeManifestReceiptMatchesOwner :
  TOE.toeFleet58ManifestAcquisitionReceipt
  ≡ Manifest.canonicalFleet58ManifestAcquisitionReceipt
toeManifestReceiptMatchesOwner = refl

unifierManifestReceiptMatchesOwner :
  Unifier.unifierFleet58ManifestAcquisitionReceipt
  ≡ Manifest.canonicalFleet58ManifestAcquisitionReceipt
unifierManifestReceiptMatchesOwner = refl

toePerGapDispatchStillBlocked :
  TOE.toeFleet58PerGapDispatchEnabled ≡ false
toePerGapDispatchStillBlocked =
  Manifest.perGapDispatchEnabledIsFalse

unifierPerGapDispatchStillBlocked :
  Unifier.unifierFleet58PerGapDispatchEnabled ≡ false
unifierPerGapDispatchStillBlocked =
  Manifest.perGapDispatchEnabledIsFalse

toeAcquisitionDoesNotPayRequirement :
  Bound.BoundDemandAutomaticallyPaysRequirement → ⊥
toeAcquisitionDoesNotPayRequirement =
  TOE.toeFleet58AcquisitionDoesNotPayRequirement

unifierAcquisitionDoesNotPayRequirement :
  Bound.BoundDemandAutomaticallyPaysRequirement → ⊥
unifierAcquisitionDoesNotPayRequirement =
  Unifier.unifierFleet58AcquisitionDoesNotPayRequirement
