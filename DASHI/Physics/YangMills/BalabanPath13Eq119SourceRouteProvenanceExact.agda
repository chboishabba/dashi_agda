{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119SourceRouteProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119) SOURCE-ROUTE PROVENANCE AUDIT
--
-- The preferred route now pushes the radius payment back into the selected
-- variational/physical representation:
--
--   selected Path13 variational representation
--     -> native radius
--     -> operator/chart compatibility
--     -> 74-link principal-image compiler.
--
-- Thus native radius is a compiler output on the preferred route.  This does
-- not construct the selected background or the physical representation facts
-- needed by that compiler.  Existence and compilation remain separate status
-- coordinates below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanCMP98Path13VariationalRadiusSourceFamilyExact as PreferredSource
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as Fibre
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as RadiusOperator
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal

record Path13Eq119SourceRouteStatus : Set where
  field
    compactFourInputAdapterClosed : Bool
    radiusNativeFourInputAdapterClosed : Bool
    variationalRadiusPreferredAdapterClosed : Bool
    selectedVariationalRadiusCompilerClosed : Bool
    selectedBackgroundRadiusSameObjectOwnershipClosed : Bool
    variationalOperatorCompatibilityCompilerClosed : Bool
    selectedOperatorChartOwnershipCompilerClosed : Bool
    nativeRadiusToOperatorDefectCompilerClosed : Bool
    nativeRadiusRelative74TelescopeClosed : Bool
    oneScalarCutThresholdAdapterClosed : Bool
    radiusPrincipalImageCompilerClosed : Bool

    independentNativeRadiusPaymentRequiredOnPreferredRoute : Bool

    selectedPath13BackgroundConstructed : Bool
    selectedVariationalRadiusRepresentationConstructed : Bool
    selectedPath13NativeRadiusConstructed : Bool
    standardRationalSU2OperatorRepresentationConstructed : Bool
    selectedOperatorChartRepresentationConstructed : Bool
    selectedCutThresholdConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool
    federbushConventionFamilyConstructed : Bool
    physicalEq119ClosedByEitherRoute : Bool

    compactFourInputAdapterClosedIsTrue : compactFourInputAdapterClosed ≡ true
    radiusNativeFourInputAdapterClosedIsTrue : radiusNativeFourInputAdapterClosed ≡ true
    variationalRadiusPreferredAdapterClosedIsTrue :
      variationalRadiusPreferredAdapterClosed ≡ true
    selectedVariationalRadiusCompilerClosedIsTrue :
      selectedVariationalRadiusCompilerClosed ≡ true
    selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue :
      selectedBackgroundRadiusSameObjectOwnershipClosed ≡ true
    variationalOperatorCompatibilityCompilerClosedIsTrue :
      variationalOperatorCompatibilityCompilerClosed ≡ true
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

    independentNativeRadiusPaymentRequiredOnPreferredRouteIsFalse :
      independentNativeRadiusPaymentRequiredOnPreferredRoute ≡ false
    selectedPath13BackgroundConstructedIsFalse : selectedPath13BackgroundConstructed ≡ false
    selectedVariationalRadiusRepresentationConstructedIsFalse :
      selectedVariationalRadiusRepresentationConstructed ≡ false
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
  ; variationalRadiusPreferredAdapterClosed = true
  ; selectedVariationalRadiusCompilerClosed = true
  ; selectedBackgroundRadiusSameObjectOwnershipClosed = true
  ; variationalOperatorCompatibilityCompilerClosed = true
  ; selectedOperatorChartOwnershipCompilerClosed = true
  ; nativeRadiusToOperatorDefectCompilerClosed = true
  ; nativeRadiusRelative74TelescopeClosed = true
  ; oneScalarCutThresholdAdapterClosed = true
  ; radiusPrincipalImageCompilerClosed = true
  ; independentNativeRadiusPaymentRequiredOnPreferredRoute = false
  ; selectedPath13BackgroundConstructed = false
  ; selectedVariationalRadiusRepresentationConstructed = false
  ; selectedPath13NativeRadiusConstructed = false
  ; standardRationalSU2OperatorRepresentationConstructed = false
  ; selectedOperatorChartRepresentationConstructed = false
  ; selectedCutThresholdConstructed = false
  ; rationalRealRingEmbeddingConstructed = false
  ; federbushConventionFamilyConstructed = false
  ; physicalEq119ClosedByEitherRoute = false
  ; compactFourInputAdapterClosedIsTrue = refl
  ; radiusNativeFourInputAdapterClosedIsTrue = refl
  ; variationalRadiusPreferredAdapterClosedIsTrue = refl
  ; selectedVariationalRadiusCompilerClosedIsTrue = refl
  ; selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue = refl
  ; variationalOperatorCompatibilityCompilerClosedIsTrue = refl
  ; selectedOperatorChartOwnershipCompilerClosedIsTrue = refl
  ; nativeRadiusToOperatorDefectCompilerClosedIsTrue = refl
  ; nativeRadiusRelative74TelescopeClosedIsTrue = refl
  ; oneScalarCutThresholdAdapterClosedIsTrue = refl
  ; radiusPrincipalImageCompilerClosedIsTrue = refl
  ; independentNativeRadiusPaymentRequiredOnPreferredRouteIsFalse = refl
  ; selectedPath13BackgroundConstructedIsFalse = refl
  ; selectedVariationalRadiusRepresentationConstructedIsFalse = refl
  ; selectedPath13NativeRadiusConstructedIsFalse = refl
  ; standardRationalSU2OperatorRepresentationConstructedIsFalse = refl
  ; selectedOperatorChartRepresentationConstructedIsFalse = refl
  ; selectedCutThresholdConstructedIsFalse = refl
  ; rationalRealRingEmbeddingConstructedIsFalse = refl
  ; federbushConventionFamilyConstructedIsFalse = refl
  ; physicalEq119ClosedByEitherRouteIsFalse = refl
  }

independentRadiusPaymentPruned :
  independentNativeRadiusPaymentRequiredOnPreferredRoute
    canonicalPath13Eq119SourceRouteStatus ≡ false
independentRadiusPaymentPruned = refl

radiusCompilerClosedWithoutExistencePromotion :
  selectedVariationalRadiusCompilerClosed
    canonicalPath13Eq119SourceRouteStatus ≡ true
radiusCompilerClosedWithoutExistencePromotion = refl

selectedVariationalRepresentationStillOpen :
  selectedVariationalRadiusRepresentationConstructed
    canonicalPath13Eq119SourceRouteStatus ≡ false
selectedVariationalRepresentationStillOpen = refl

radiusStillNotGloballyConstructed :
  selectedPath13NativeRadiusConstructed
    canonicalPath13Eq119SourceRouteStatus ≡ false
radiusStillNotGloballyConstructed = refl

oneScalarCutStillUninhabited :
  selectedCutThresholdConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
oneScalarCutStillUninhabited = refl

standardRepresentationStillImported :
  standardRationalSU2OperatorRepresentationConstructed
    canonicalPath13Eq119SourceRouteStatus ≡ false
standardRepresentationStillImported = refl

cmp98Path13Eq119SourceRouteProvenanceLevel : ProofLevel
cmp98Path13Eq119SourceRouteProvenanceLevel = machineChecked

selectedVariationalRadiusCompilerLevel : ProofLevel
selectedVariationalRadiusCompilerLevel =
  VariationalRadius.cmp98Path13SelectedVariationalRadiusCompilerLevel

selectedBackgroundRadiusFibreLevel : ProofLevel
selectedBackgroundRadiusFibreLevel = Fibre.cmp98Path13SelectedBackgroundRadiusFibreLevel

variationalOperatorCompatibilityLevel : ProofLevel
variationalOperatorCompatibilityLevel =
  OperatorChart.cmp98Path13VariationalOperatorRepresentationCompilerLevel

selectedOperatorChartOwnershipLevel : ProofLevel
selectedOperatorChartOwnershipLevel =
  OperatorChart.cmp98Path13SelectedOperatorChartRepresentationLevel

preferredVariationalRadiusSourceAdapterLevel : ProofLevel
preferredVariationalRadiusSourceAdapterLevel =
  PreferredSource.cmp98Path13VariationalRadiusSourceAdapterLevel

radiusNativeSourceAdapterLevel : ProofLevel
radiusNativeSourceAdapterLevel = Source.cmp98Path13RadiusNativeSourceAdapterLevel

radiusNativeOperatorCompilerLevel : ProofLevel
radiusNativeOperatorCompilerLevel = RadiusOperator.path13NativeRadiusToOperatorDefectLevel

radiusNativeCutThresholdAdapterLevel : ProofLevel
radiusNativeCutThresholdAdapterLevel =
  RadiusPrincipal.cmp98Path13OperatorChartCutThresholdAdapterLevel

radiusNativePrincipalImageCompilerLevel : ProofLevel
radiusNativePrincipalImageCompilerLevel = RadiusPrincipal.cmp98Path13RadiusPrincipalImageCompilerLevel
