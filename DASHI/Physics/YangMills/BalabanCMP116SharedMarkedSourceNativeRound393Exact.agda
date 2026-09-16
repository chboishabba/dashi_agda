{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedMarkedSourceNativeRound393Exact where

------------------------------------------------------------------------
-- ROUND393 / SOURCE-OWNED LOCALIZATION, SELECTED APPLICATION STILL PHYSICAL
--
-- R387--R392 remove two historical overpayments from the direct CMP116 B route:
--
--   * the fast ratio need not be fixed to 1/2;
--   * selected source/physical/spectral distances need not be equal.
--
-- Earlier source archaeology already established something equally important:
-- CMP116 Sect. 1 / (1.23)--(1.36) owns differentiated exponential
-- localization itself.  R338 states that theorem directly on the canonical
-- common domain, while R339/R344 isolate the remaining selected application.
--
-- Therefore the current frontier must NOT be phrased as "prove a new CMP116
-- localization theorem".  The live selected-source payments are:
--
--   P0  instantiate/align the proof-bearing CMP116 differentiated theorem on
--       the literal selected mixed-J response and a usable source envelope;
--   P1  extract/calibrate a cutoff-uniform source-native prefactor and q_fast;
--   P2  prove only the selected one-sided carrier geometry required by R392;
--   P3  identify q_fast with the reconstructed spectral semantics strongly
--       enough to obtain q_fast < q_subgap for an alleged positive subgap mode.
--
-- Finite->continuum covariance transport and the subgap contradiction are
-- already compiler-owned on the R391/R387 route once these inputs are supplied.
--
-- PRIMARY SOURCE
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Source neighbourhood: Sect. 1, especially differentiated/Cauchy localization
-- (1.23) and the positive exponential localization sum around (1.29)--(1.36).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedT5ApplicationRound339Exact as R339
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Exact as R344
import DASHI.Physics.YangMills.BalabanSourceNativeGeometricSeparationRound387Exact as R387
import DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierLowerRound392Exact as R392

------------------------------------------------------------------------
-- Source / compiler / physical-payment classification.
------------------------------------------------------------------------

cmp116DifferentiatedLocalizationSourceAuthorityLevel : ProofLevel
cmp116DifferentiatedLocalizationSourceAuthorityLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

canonicalCommonDomainSourceAlignmentLevel : ProofLevel
canonicalCommonDomainSourceAlignmentLevel =
  R338.round338LocalCanonicalSourceAlignmentLevel

selectedMagnitudeSameObjectLevel : ProofLevel
selectedMagnitudeSameObjectLevel =
  R339.round339SourceMagnitudeSameObjectLevel

selectedEnvelopeCalibrationLevel : ProofLevel
selectedEnvelopeCalibrationLevel =
  R339.round339SourceEnvelopeCalibrationLevel

literalSelectedLocalizationLevel : ProofLevel
literalSelectedLocalizationLevel =
  R344.round344LiteralSelectedLocalizationLevel

selectedCarrierLowerGeometryLevel : ProofLevel
selectedCarrierLowerGeometryLevel = conditional

sourceNativeRateCalibrationLevel : ProofLevel
sourceNativeRateCalibrationLevel = conditional

sourceRateToReconstructedSpectrumLevel : ProofLevel
sourceRateToReconstructedSpectrumLevel = conditional

------------------------------------------------------------------------
-- Pareto / authority flags pinned by the focused validation root.
------------------------------------------------------------------------

fixedHalfNormalizationMandatory : Bool
fixedHalfNormalizationMandatory = false

fixedHalfNormalizationMandatoryIsFalse :
  fixedHalfNormalizationMandatory ≡ false
fixedHalfNormalizationMandatoryIsFalse = refl

exactSelectedDistanceEqualityMandatory : Bool
exactSelectedDistanceEqualityMandatory = false

exactSelectedDistanceEqualityMandatoryIsFalse :
  exactSelectedDistanceEqualityMandatory ≡ false
exactSelectedDistanceEqualityMandatoryIsFalse = refl

cmp116DifferentiatedLocalizationReprovedHere : Bool
cmp116DifferentiatedLocalizationReprovedHere = false

cmp116DifferentiatedLocalizationReprovedHereIsFalse :
  cmp116DifferentiatedLocalizationReprovedHere ≡ false
cmp116DifferentiatedLocalizationReprovedHereIsFalse = refl

oneSidedSelectedCarrierGeometryStillProofBearing : Bool
oneSidedSelectedCarrierGeometryStillProofBearing = true

oneSidedSelectedCarrierGeometryStillProofBearingIsTrue :
  oneSidedSelectedCarrierGeometryStillProofBearing ≡ true
oneSidedSelectedCarrierGeometryStillProofBearingIsTrue = refl

sourceNativeRateCalibrationStillProofBearing : Bool
sourceNativeRateCalibrationStillProofBearing = true

sourceNativeRateCalibrationStillProofBearingIsTrue :
  sourceNativeRateCalibrationStillProofBearing ≡ true
sourceNativeRateCalibrationStillProofBearingIsTrue = refl

selectedSourceApplicationStillProofBearing : Bool
selectedSourceApplicationStillProofBearing = true

selectedSourceApplicationStillProofBearingIsTrue :
  selectedSourceApplicationStillProofBearing ≡ true
selectedSourceApplicationStillProofBearingIsTrue = refl

historicalSensitivityRouteMandatory : Bool
historicalSensitivityRouteMandatory = false

historicalSensitivityRouteMandatoryIsFalse :
  historicalSensitivityRouteMandatory ≡ false
historicalSensitivityRouteMandatoryIsFalse = refl

round393FrontierRecutCompilerLevel : ProofLevel
round393FrontierRecutCompilerLevel = machineChecked

record Round393Boundary : Set where
  constructor round393-boundary
  field
    publishedLocalizationOwnedUpstream : Bool
    publishedLocalizationOwnedUpstreamIsTrue :
      publishedLocalizationOwnedUpstream ≡ true

    sourceNativeRatioRetained : Bool
    sourceNativeRatioRetainedIsTrue : sourceNativeRatioRetained ≡ true

    exactDistanceWeldsPruned : Bool
    exactDistanceWeldsPrunedIsTrue : exactDistanceWeldsPruned ≡ true

    selectedApplicationAndGeometryRemainPhysical : Bool
    selectedApplicationAndGeometryRemainPhysicalIsTrue :
      selectedApplicationAndGeometryRemainPhysical ≡ true

canonicalRound393Boundary : Round393Boundary
canonicalRound393Boundary =
  round393-boundary true refl true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
