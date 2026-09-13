module DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO

desiDR2BAOSource : Source.AttributedSource
desiDR2BAOSource =
  Source.mkDOISource
    "DESI Collaboration; M. Abdul Karim et al."
    "DESI DR2 Results II: Measurements of Baryon Acoustic Oscillations and Cosmological Constraints"
    "Physical Review D 112, 083515"
    "2025"
    "10.1103/tr6y-kpc6"
    "https://doi.org/10.1103/tr6y-kpc6"
    Source.academicArticleSource
    "primary DESI DR2 BAO measurement source for tracer-indexed effective-redshift distance coordinates and their reported correlations"
    Source.publicAttribution

data DESIDR2TracerBin : Set where
  lrg1 : DESIDR2TracerBin
  lrg2 : DESIDR2TracerBin
  lrg3Elg1 : DESIDR2TracerBin
  elg2 : DESIDR2TracerBin
  qso : DESIDR2TracerBin
  lya : DESIDR2TracerBin

effectiveRedshiftMilli : DESIDR2TracerBin → Nat
effectiveRedshiftMilli lrg1 = 510
effectiveRedshiftMilli lrg2 = 706
effectiveRedshiftMilli lrg3Elg1 = 934
effectiveRedshiftMilli elg2 = 1321
effectiveRedshiftMilli qso = 1484
effectiveRedshiftMilli lya = 2330

record SharedBAOObservationKey : Set where
  constructor sharedBAOObservationKey
  field
    datasetSource : Source.AttributedSource
    datasetRevision : String
    tracerBin : DESIDR2TracerBin
    redshiftMilli : Nat
    observable : SharedBAO.SharedBAOObservable

open SharedBAOObservationKey public

mkDR2Key :
  DESIDR2TracerBin →
  SharedBAO.SharedBAOObservable →
  SharedBAOObservationKey
mkDR2Key tracer observable =
  sharedBAOObservationKey
    desiDR2BAOSource
    "DESI DR2 / Phys. Rev. D 112, 083515 (2025)"
    tracer
    (effectiveRedshiftMilli tracer)
    observable

lrg1TransverseKey : SharedBAOObservationKey
lrg1TransverseKey = mkDR2Key lrg1 SharedBAO.transverseDMOverRd

lrg1RadialKey : SharedBAOObservationKey
lrg1RadialKey = mkDR2Key lrg1 SharedBAO.radialDHOverRd

lrg2TransverseKey : SharedBAOObservationKey
lrg2TransverseKey = mkDR2Key lrg2 SharedBAO.transverseDMOverRd

lrg2RadialKey : SharedBAOObservationKey
lrg2RadialKey = mkDR2Key lrg2 SharedBAO.radialDHOverRd

lrg3Elg1TransverseKey : SharedBAOObservationKey
lrg3Elg1TransverseKey = mkDR2Key lrg3Elg1 SharedBAO.transverseDMOverRd

lrg3Elg1RadialKey : SharedBAOObservationKey
lrg3Elg1RadialKey = mkDR2Key lrg3Elg1 SharedBAO.radialDHOverRd

elg2TransverseKey : SharedBAOObservationKey
elg2TransverseKey = mkDR2Key elg2 SharedBAO.transverseDMOverRd

elg2RadialKey : SharedBAOObservationKey
elg2RadialKey = mkDR2Key elg2 SharedBAO.radialDHOverRd

qsoTransverseKey : SharedBAOObservationKey
qsoTransverseKey = mkDR2Key qso SharedBAO.transverseDMOverRd

qsoRadialKey : SharedBAOObservationKey
qsoRadialKey = mkDR2Key qso SharedBAO.radialDHOverRd

lyaTransverseKey : SharedBAOObservationKey
lyaTransverseKey = mkDR2Key lya SharedBAO.transverseDMOverRd

lyaRadialKey : SharedBAOObservationKey
lyaRadialKey = mkDR2Key lya SharedBAO.radialDHOverRd

record SameObservationKeyRequirement
    (left right : SharedBAOObservationKey) : Set where
  constructor sameObservationKeyRequirement
  field
    sameObservationKey : left ≡ right

open SameObservationKeyRequirement public

data SameObservableDifferentKeyIsSameObservationPermission : Set where

sameObservableDifferentKeyIsNotSameObservation :
  SameObservableDifferentKeyIsSameObservationPermission → ⊥
sameObservableDifferentKeyIsNotSameObservation ()

record SharedBAOObservationKeyStatus : Set where
  constructor sharedBAOObservationKeyStatus
  field
    datasetRevisionPinned : Bool
    tracerBinPinned : Bool
    effectiveRedshiftPinned : Bool
    observablePinned : Bool
    sharedObservationKeyIdentityEstablished : Bool
    covarianceMatrixWelded : Bool
    bothModelsNumericallyPredictedSameKey : Bool
    sameKeyNumericalSeparationLocked : Bool

open SharedBAOObservationKeyStatus public

canonicalSharedBAOObservationKeyStatus : SharedBAOObservationKeyStatus
canonicalSharedBAOObservationKeyStatus =
  sharedBAOObservationKeyStatus true true true true true false false false

sharedObservationKeyIdentityPaid :
  sharedObservationKeyIdentityEstablished canonicalSharedBAOObservationKeyStatus
  ≡ true
sharedObservationKeyIdentityPaid = refl

sameKeyNumericalModelPredictionsStillOpen :
  sameKeyNumericalSeparationLocked canonicalSharedBAOObservationKeyStatus
  ≡ false
sameKeyNumericalModelPredictionsStillOpen = refl
