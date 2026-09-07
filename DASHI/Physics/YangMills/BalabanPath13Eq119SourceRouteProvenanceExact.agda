{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119SourceRouteProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119) SOURCE-ROUTE PROVENANCE AUDIT
--
-- Both preferred routes now have four top-level coordinated inputs.
--
-- Compact route:
--   selected background
--   + scalar embedding
--   + Federbush family
--   + one dependent mixed cut/defect weld.
--
-- Radius-native route:
--   selected background/radius/operator-chart representation fibre
--   + scalar embedding
--   + Federbush family
--   + one scalar cut residual: 1/24 <= r_cut.
--
-- The second route does not construct any of those physical/analytic inputs.
-- Its gain is attribution and same-object ownership: physical smallness is the
-- native Path13 radius already consumed by coercivity, standard operator
-- representation is explicit, selected defect/order identification is attached
-- to the selected physical background, and cut authority is only the scalar
-- inclusion actually specific to the selected chart.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as Fibre
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as RadiusOperator
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal

record Path13Eq119SourceRouteStatus : Set where
  field
    compactFourInputAdapterClosed : Bool
    radiusNativeFourInputAdapterClosed : Bool
    selectedBackgroundRadiusSameObjectOwnershipClosed : Bool
    selectedOperatorChartOwnershipCompilerClosed : Bool
    nativeRadiusToOperatorDefectCompilerClosed : Bool
    nativeRadiusRelative74TelescopeClosed : Bool
    oneScalarCutThresholdAdapterClosed : Bool
    radiusPrincipalImageCompilerClosed : Bool

    selectedPath13BackgroundConstructed : Bool
    selectedPath13NativeRadiusConstructed : Bool
    standardRationalSU2OperatorRepresentationConstructed : Bool
    selectedOperatorChartRepresentationConstructed : Bool
    selectedCutThresholdConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool
    federbushConventionFamilyConstructed : Bool
    physicalEq119ClosedByEitherRoute : Bool

    compactFourInputAdapterClosedIsTrue : compactFourInputAdapterClosed ≡ true
    radiusNativeFourInputAdapterClosedIsTrue : radiusNativeFourInputAdapterClosed ≡ true
    selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue :
      selectedBackgroundRadiusSameObjectOwnershipClosed ≡ true
    selectedOperatorChartOwnershipCompilerClosedIsTrue :
      selectedOperatorChartOwnershipCompilerClosed ≡ true
    nativeRadiusToOperatorDefectCompilerClosedIsTrue :
      nativeRadiusToOperatorDefectCompilerClosed ≡ true
    nativeRadiusRelative74TelescopeClosedIsTrue :
      nativeRadiusRelative74TelescopeClosed ≡ true
    oneScalarCutThresholdAdapterClosedIsTrue :
      oneScalarCutThresholdAdapterClosed ≡ true
    radiusPrincipalImageCompilerClosedIsTrue :
      radiusPrincipalImageCompilerClosed ≡ true

    selectedPath13BackgroundConstructedIsFalse : selectedPath13BackgroundConstructed ≡ false
    selectedPath13NativeRadiusConstructedIsFalse : selectedPath13NativeRadiusConstructed ≡ false
    standardRationalSU2OperatorRepresentationConstructedIsFalse :
      standardRationalSU2OperatorRepresentationConstructed ≡ false
    selectedOperatorChartRepresentationConstructedIsFalse :
      selectedOperatorChartRepresentationConstructed ≡ false
    selectedCutThresholdConstructedIsFalse : selectedCutThresholdConstructed ≡ false
    rationalRealRingEmbeddingConstructedIsFalse : rationalRealRingEmbeddingConstructed ≡ false
    federbushConventionFamilyConstructedIsFalse : federbushConventionFamilyConstructed ≡ false
    physicalEq119ClosedByEitherRouteIsFalse : physicalEq119ClosedByEitherRoute ≡ false

open Path13Eq119SourceRouteStatus public

canonicalPath13Eq119SourceRouteStatus : Path13Eq119SourceRouteStatus
canonicalPath13Eq119SourceRouteStatus = record
  { compactFourInputAdapterClosed = true
  ; radiusNativeFourInputAdapterClosed = true
  ; selectedBackgroundRadiusSameObjectOwnershipClosed = true
  ; selectedOperatorChartOwnershipCompilerClosed = true
  ; nativeRadiusToOperatorDefectCompilerClosed = true
  ; nativeRadiusRelative74TelescopeClosed = true
  ; oneScalarCutThresholdAdapterClosed = true
  ; radiusPrincipalImageCompilerClosed = true
  ; selectedPath13BackgroundConstructed = false
  ; selectedPath13NativeRadiusConstructed = false
  ; standardRationalSU2OperatorRepresentationConstructed = false
  ; selectedOperatorChartRepresentationConstructed = false
  ; selectedCutThresholdConstructed = false
  ; rationalRealRingEmbeddingConstructed = false
  ; federbushConventionFamilyConstructed = false
  ; physicalEq119ClosedByEitherRoute = false
  ; compactFourInputAdapterClosedIsTrue = refl
  ; radiusNativeFourInputAdapterClosedIsTrue = refl
  ; selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue = refl
  ; selectedOperatorChartOwnershipCompilerClosedIsTrue = refl
  ; nativeRadiusToOperatorDefectCompilerClosedIsTrue = refl
  ; nativeRadiusRelative74TelescopeClosedIsTrue = refl
  ; oneScalarCutThresholdAdapterClosedIsTrue = refl
  ; radiusPrincipalImageCompilerClosedIsTrue = refl
  ; selectedPath13BackgroundConstructedIsFalse = refl
  ; selectedPath13NativeRadiusConstructedIsFalse = refl
  ; standardRationalSU2OperatorRepresentationConstructedIsFalse = refl
  ; selectedOperatorChartRepresentationConstructedIsFalse = refl
  ; selectedCutThresholdConstructedIsFalse = refl
  ; rationalRealRingEmbeddingConstructedIsFalse = refl
  ; federbushConventionFamilyConstructedIsFalse = refl
  ; physicalEq119ClosedByEitherRouteIsFalse = refl
  }

ownershipDoesNotConstructRadius :
  selectedBackgroundRadiusSameObjectOwnershipClosed canonicalPath13Eq119SourceRouteStatus ≡ true
ownershipDoesNotConstructRadius = refl

radiusStillUninhabited :
  selectedPath13NativeRadiusConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
radiusStillUninhabited = refl

operatorChartStillUninhabited :
  selectedOperatorChartRepresentationConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
operatorChartStillUninhabited = refl

oneScalarCutStillUninhabited :
  selectedCutThresholdConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
oneScalarCutStillUninhabited = refl

standardRepresentationStillImported :
  standardRationalSU2OperatorRepresentationConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
standardRepresentationStillImported = refl

cmp98Path13Eq119SourceRouteProvenanceLevel : ProofLevel
cmp98Path13Eq119SourceRouteProvenanceLevel = machineChecked

selectedBackgroundRadiusFibreLevel : ProofLevel
selectedBackgroundRadiusFibreLevel = Fibre.cmp98Path13SelectedBackgroundRadiusFibreLevel

selectedOperatorChartOwnershipLevel : ProofLevel
selectedOperatorChartOwnershipLevel =
  OperatorChart.cmp98Path13SelectedOperatorChartRepresentationLevel

radiusNativeSourceAdapterLevel : ProofLevel
radiusNativeSourceAdapterLevel = Source.cmp98Path13RadiusNativeSourceAdapterLevel

radiusNativeOperatorCompilerLevel : ProofLevel
radiusNativeOperatorCompilerLevel = RadiusOperator.path13NativeRadiusToOperatorDefectLevel

radiusNativeCutThresholdAdapterLevel : ProofLevel
radiusNativeCutThresholdAdapterLevel =
  RadiusPrincipal.cmp98Path13OperatorChartCutThresholdAdapterLevel

radiusNativePrincipalImageCompilerLevel : ProofLevel
radiusNativePrincipalImageCompilerLevel = RadiusPrincipal.cmp98Path13RadiusPrincipalImageCompilerLevel
