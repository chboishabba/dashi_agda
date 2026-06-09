module DASHI.Physics.Closure.YMSprint105SymmetryRestorationContinuumLimit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Sprint 105, Worker 3:
-- symmetry-restoration route to Poincare covariance and the spectrum
-- condition.
--
-- This module is an obligation surface, not a closed proof.  It records that
-- the spatial-only construction has H3 symmetry with an untouched time
-- coordinate during construction, and that the continuum route must restore
-- SO4 before downstream Poincare covariance and spectrum-condition claims can
-- be closed.
--
-- No Clay/Yang-Mills promotion is made here.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

symmetryRestorationClosedInRepo : Bool
symmetryRestorationClosedInRepo = false

poincareCovarianceClosedInRepo : Bool
poincareCovarianceClosedInRepo = false

spectrumConditionClosedInRepo : Bool
spectrumConditionClosedInRepo = false

spatialDimension : Nat
spatialDimension = 3

euclideanContinuumDimension : Nat
euclideanContinuumDimension = 4

h3AnisotropicLatticeText : String
h3AnisotropicLatticeText =
  "Spatial-only blocking acts on H3 and leaves the time coordinate as id_time during construction."

h3BreaksH4Text : String
h3BreaksH4Text =
  "The construction symmetry is H3 x id_time, so finite-cutoff H4 symmetry is broken during the blocked-lattice construction."

so4RestorationObligationText : String
so4RestorationObligationText =
  "SymmetryRestorationInContinuumLimit : H3AnisotropicLattice -> SO4SymmetricContinuum is a DASHI-native theorem obligation: as a -> 0 the anisotropic H3 x id_time construction must restore SO4 covariance."

poincareCovarianceDependencyText : String
poincareCovarianceDependencyText =
  "Poincare covariance is downstream of continuum SO4 restoration plus OS/Wightman reconstruction; it is required here but not proved here."

spectrumConditionDependencyText : String
spectrumConditionDependencyText =
  "The spectrum condition is downstream of the restored-covariant Wightman reconstruction; it is required here but not proved here."

record H3AnisotropicLattice : Set where
  constructor mkH3AnisotropicLattice
  field
    spatialBlockingGroup :
      String
    untouchedTimeCoordinate :
      String
    constructionSymmetry :
      String
    spatialDimensionRecorded :
      Nat
    spatialDimensionIsThree :
      spatialDimensionRecorded ≡ spatialDimension
    h4BrokenDuringConstruction :
      Bool
    h4BrokenDuringConstructionIsTrue :
      h4BrokenDuringConstruction ≡ true
    h3TimesIdTimeRecorded :
      Bool
    h3TimesIdTimeRecordedIsTrue :
      h3TimesIdTimeRecorded ≡ true
    constructionText :
      String
    constructionTextIsCanonical :
      constructionText ≡ h3AnisotropicLatticeText
    h4BreakingText :
      String
    h4BreakingTextIsCanonical :
      h4BreakingText ≡ h3BreaksH4Text

record SO4SymmetricContinuum : Set where
  constructor mkSO4SymmetricContinuum
  field
    sourceLattice :
      H3AnisotropicLattice
    targetSymmetry :
      String
    continuumDimensionRecorded :
      Nat
    continuumDimensionIsFour :
      continuumDimensionRecorded ≡ euclideanContinuumDimension
    restorationRequired :
      Bool
    restorationRequiredIsTrue :
      restorationRequired ≡ true
    restorationClosed :
      Bool
    restorationClosedIsFalse :
      restorationClosed ≡ false
    theoremObligation :
      String
    theoremObligationIsCanonical :
      theoremObligation ≡ so4RestorationObligationText
    obligationStatus :
      String

SymmetryRestorationInContinuumLimit :
  H3AnisotropicLattice →
  SO4SymmetricContinuum
SymmetryRestorationInContinuumLimit lattice =
  mkSO4SymmetricContinuum
    lattice
    "SO4"
    euclideanContinuumDimension
    refl
    true
    refl
    false
    refl
    so4RestorationObligationText
    refl
    "required-open"

record PoincareCovarianceStatus : Set where
  constructor mkPoincareCovarianceStatus
  field
    continuumSymmetry :
      SO4SymmetricContinuum
    requiredDownstream :
      Bool
    requiredDownstreamIsTrue :
      requiredDownstream ≡ true
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    dependsOnSO4Restoration :
      SO4SymmetricContinuum.restorationRequired continuumSymmetry ≡ true
    blockedByOpenSO4Restoration :
      SO4SymmetricContinuum.restorationClosed continuumSymmetry ≡ false
    dependencyText :
      String
    dependencyTextIsCanonical :
      dependencyText ≡ poincareCovarianceDependencyText

record SpectrumConditionStatus : Set where
  constructor mkSpectrumConditionStatus
  field
    poincareCovariance :
      PoincareCovarianceStatus
    requiredDownstream :
      Bool
    requiredDownstreamIsTrue :
      requiredDownstream ≡ true
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    dependsOnPoincareCovariance :
      PoincareCovarianceStatus.requiredDownstream poincareCovariance ≡ true
    blockedByOpenPoincareCovariance :
      PoincareCovarianceStatus.closedHere poincareCovariance ≡ false
    dependencyText :
      String
    dependencyTextIsCanonical :
      dependencyText ≡ spectrumConditionDependencyText

canonicalH3AnisotropicLattice :
  H3AnisotropicLattice
canonicalH3AnisotropicLattice =
  mkH3AnisotropicLattice
    "H3"
    "id_time"
    "H3 x id_time"
    spatialDimension
    refl
    true
    refl
    true
    refl
    h3AnisotropicLatticeText
    refl
    h3BreaksH4Text
    refl

canonicalSO4SymmetricContinuum :
  SO4SymmetricContinuum
canonicalSO4SymmetricContinuum =
  SymmetryRestorationInContinuumLimit canonicalH3AnisotropicLattice

canonicalPoincareCovarianceStatus :
  PoincareCovarianceStatus
canonicalPoincareCovarianceStatus =
  mkPoincareCovarianceStatus
    canonicalSO4SymmetricContinuum
    true
    refl
    false
    refl
    refl
    refl
    poincareCovarianceDependencyText
    refl

canonicalSpectrumConditionStatus :
  SpectrumConditionStatus
canonicalSpectrumConditionStatus =
  mkSpectrumConditionStatus
    canonicalPoincareCovarianceStatus
    true
    refl
    false
    refl
    refl
    refl
    spectrumConditionDependencyText
    refl

record YMSprint105SymmetryRestorationContinuumLimitReceipt : Set where
  constructor mkYMSprint105SymmetryRestorationContinuumLimitReceipt
  field
    h3AnisotropicLattice :
      H3AnisotropicLattice
    so4SymmetricContinuum :
      SO4SymmetricContinuum
    poincareCovarianceStatus :
      PoincareCovarianceStatus
    spectrumConditionStatus :
      SpectrumConditionStatus
    restorationObligationFunction :
      H3AnisotropicLattice →
      SO4SymmetricContinuum
    restorationObligationFunctionIsCanonical :
      restorationObligationFunction ≡ SymmetryRestorationInContinuumLimit
    constructionBreaksH4 :
      H3AnisotropicLattice.h4BrokenDuringConstruction h3AnisotropicLattice
      ≡ true
    constructionKeepsH3TimesIdTime :
      H3AnisotropicLattice.h3TimesIdTimeRecorded h3AnisotropicLattice
      ≡ true
    continuumRestorationRequired :
      SO4SymmetricContinuum.restorationRequired so4SymmetricContinuum
      ≡ true
    continuumRestorationStillOpen :
      SO4SymmetricContinuum.restorationClosed so4SymmetricContinuum
      ≡ false
    poincareCovarianceRequired :
      PoincareCovarianceStatus.requiredDownstream poincareCovarianceStatus
      ≡ true
    poincareCovarianceStillOpen :
      PoincareCovarianceStatus.closedHere poincareCovarianceStatus
      ≡ false
    spectrumConditionRequired :
      SpectrumConditionStatus.requiredDownstream spectrumConditionStatus
      ≡ true
    spectrumConditionStillOpen :
      SpectrumConditionStatus.closedHere spectrumConditionStatus
      ≡ false
    restorationClosedFlag :
      symmetryRestorationClosedInRepo ≡ false
    poincareClosedFlag :
      poincareCovarianceClosedInRepo ≡ false
    spectrumClosedFlag :
      spectrumConditionClosedInRepo ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint105SymmetryRestorationContinuumLimitReceipt :
  YMSprint105SymmetryRestorationContinuumLimitReceipt
canonicalYMSprint105SymmetryRestorationContinuumLimitReceipt =
  mkYMSprint105SymmetryRestorationContinuumLimitReceipt
    canonicalH3AnisotropicLattice
    canonicalSO4SymmetricContinuum
    canonicalPoincareCovarianceStatus
    canonicalSpectrumConditionStatus
    SymmetryRestorationInContinuumLimit
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalReceiptKeepsClayFalse :
  clayYangMillsPromoted ≡ false
canonicalReceiptKeepsClayFalse =
  refl
